from tkinter import *
from tkinter import ttk,filedialog,simpledialog
import tkinter.messagebox as msgbox
import os
from PIL import Image,ImageTk,ImageDraw,ImageEnhance,ImageOps
import numpy as np
import cv2
import pytesseract
import sqlite3
import datetime
import threading
import fitz
import time
import gc

getting_started_Text="""DocScanner is an Light Weight but an powerful Image Scanner which runs on your desktop available for Windows. It comes with Built-in support for the JPG and PNG Image Extensions
It Helps the users to manipulate Scanned Images into Softcopy such as the PDF. OCR(Optical Character Recognition) is an another additional feature for the DocScanner to abstract the Text from the Image.
➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖➖
Note - 
1 While Shifting the OCR Window back to SCAN or HOME window the Image Filter will be back to Original.

2 Press the Ok Button of the Preview scan window only for the OCR Scan. It is not necessary for the user to use the preview scan for export of image or ADD because it will process from the user settings.

3 Poppler must be installed to import the PDF
"""

Steps_Text="""
1 Import -> The Initial and import step to use DocScanner is to import the Images from your system. Click the Import Button at Top-Right corner to import images.

2 Webcam Step -> If you Have a Webcam or an video link which you want to capture the image for the Document Scanner. Click Webcam button on Top-Right corner and insert the video link and click start button.click the capture button to save the frame of video and click stop button to stop the webcam

3 Home -> The Home Button on the Left-Side corner will switch the window to the Home Window.

4 Scan -> The Scan Button on the Left-Side corner will switch the window to the Scan Window. If the Images are Import.

5 OCR -> The OCR Button on the Left-Side corner will switch the window to the OCR Window. If the Images are Import.

6 Records -> The Record Button on the Left-Side corner will switch the window to the Records Window. Which will display the history of your activities.

7 Reset -> The Reset Button on the Left-Side corner will reset the DocScanner.

8 Setting -> To Configure the user based Image Filter/Effect and specify the height and width of the image. The User can Reset the ADD list and set the Full Screen mode for user friendly experience.

9 ADD (➕) -> The ADD button in the scan window will Add the current Image and its image effects to the list which would be essential for the creation of PDF.

10 Export PDF -> The Export PDF button will create an pdf from the ADD list image/images.

11 Export Image -> The Export Image Button will be used to save the manipulate image

12 Export ADD List -> This Button would be helpful to export all elements of the ADD List as an Image and not by an PDF.

13 Rotate -> This button will rotate the image to the left side.

14 ➕🔍 -> Increase the Height and width of the image with the proper ratio.

15 ➖🔍 -> Decrease the Height and width of the image with the proper ratio.

16 Edit List -> This will popup the Edit Window in which the user will be able to edit the ADD list. Such as to remove the image from the list or to replace the image. User will also be able to export a particular image from the list.

17 Run OCR -> This button will initialize the OCR process of the given image and try to abstract the text as much as possible after that the abstracted text will be displayed to the right side text box in the OCR Window.

18 Preview Scan -> This will help the User to take a demo scan for the image before taking any processing.

19 Next ▶ -> The Next button will go for the Next image.

20 ◀ Previous -> The Next button will go for the Previous image.
"""
############################################################### USER Class ###############################################################
class User:
    def __init__(self):
        self.Org_List=[]
        self.PDF_ADD_LIST=[]
        self.EDIT_PDF_LIST=[]
        self.title="Document Scanner"
        self.IMG_FORMAT=[".png",".jpeg",".jpg"]
        self.APP_LOGO = "Capture.ico"

        self.Home_Active=True
        self.SCAN_Active=False
        self.OCR_Active=False
        self.Export_Active=False
        self.Status_Active=False
        self.Setting_Active=False
        self.PDF_Active=False
        self.SideTOOL_Active = True

        self.C1=[0,0]
        self.C2=[80,0]
        self.C3=[80,80]
        self.C4=[0,80]
        self.Circle_Radius=7
        self.C1_cirlce=None
        self.C2_cirlce=None
        self.C3_cirlce=None
        self.C4_cirlce=None

        self.Poly=None

        self.ROTATION_List=[0,90,180,270,360]
        self.Rotate_Point=0

        self.Fixed_SIZE=700
        self.Constant_Size=10

        self.Size_Ratio=0.1
        self.Constant_Size=0.7
        self.fixed_ratio=self.Constant_Size
        self.Constant_size_Active=False

        self.DataBase_DIR=os.environ['USERPROFILE'].replace("\\","/")
        self.DataBase_FILE=f"{self.DataBase_DIR}/DocScan.db"
        self.Data_TABLE="Records"

        self.WebCam_Folder_Name="Camera_DocScan"
        self.Backup_Folder="Backups_DocScan"

        self.backup_path_part1=os.path.dirname(self.DataBase_FILE).replace('\\','/')
        self.Backup_Path=f"{self.backup_path_part1}/{self.Backup_Folder}"

        self.Webcam_On=False
        self.WebCam_Capture_NO=1
        self.insert_urls=""

        self.Image_Effect_Number=0

        self.Fixed_PDF_PAGE=False
        self.PDF_Height=1648
        self.PDF_Width=1190

        self.Image_Height=0
        self.Image_Width=0

        self.Edit_Pointer=0
        self.Edit_WIN=True
        self.wanted_dpi = 200

        self.PDF_EDIT_Pointer=0
        self.PDF_Reset_Active=False

        self.FullScreen_Active=False
        
        self.Shortcut_Patterns=["Ctrl + O","Ctrl + Shift + H","Ctrl + Shift + S","Ctrl + Shift + O","Ctrl + Shift + R","Ctrl + Shift + P","Ctrl + W","Ctrl + A","Ctrl +","Ctrl -","Left Key","Right Key","Ctrl + T","Ctrl + P","Ctrl + S","F1","Ctrl + K","F5"]
        self.Shortcut_Desc=["Import Images","Open Home Window","Open Scan Window","Open OCR Window","Open Records Window","Open PDF Edit","Rotate Image","ADD Image","Zoom IN Image","Zoom OUT Image","Previous Image","Next Image","Add to OCR","Preview Scan","Settings Window","Run OCR","Keyboard Shortcut","Full Screen"]

        self.Sharpen_NO=4
        self.Contrast_NO=2
        self.Thresh_NO=17
        self.Blut_NO=3
        self.Gamma_NO=0.5
        self.Bright_NO=50

        self.Thumbnail_Range=(680,500)

        self.Save_Records=True
        self.Auto_Scan_Active=True
        self.total_pdf_pages=0

        self.TESSERACT_PATH = "Tesseract-OCR/tesseract.exe"
        pass

    #----------User Interface FrontEnd----------
    def User_Interface(self,*args):
        self.root=Tk()
        self.root.title(self.title)
        self.root.state("zoomed")
        self.root.columnconfigure(0,weight=1)
        self.root.rowconfigure(0,weight=1)
        self.root.tk.call('encoding', 'system', 'utf-8')
        self.root.wm_protocol("WM_DELETE_WINDOW",self.Exit_FUNC)
        try:
            self.root.wm_iconbitmap(self.APP_LOGO)
        except:
            pass
        # styles
        self.STYLE=ttk.Style()

        # button style
        self.STYLE.element_create("TButton","from","winnative")
        self.STYLE.element_create("TButton.button","from","winnative")
        self.STYLE.element_create("TButton.focus","from","winnative")
        self.STYLE.element_create("TButton.padding","from","winnative")
        self.STYLE.element_create("TButton.label","from","winnative")
        self.STYLE.layout("TButton",[('TButton.button', 
        {'sticky': 'nswe', 'children': [('TButton.focus', 
        {'sticky': 'nswe', 'children': [('TButton.padding',
        {'sticky': 'nswe', 'children': [('TButton.label', 
        {'sticky': 'nswe'})]})]})]})])
        self.STYLE.configure("TButton",background="#6c09ed",borderwidth=2,relief=SOLID,foreground="yellow",font=("arial",11,"bold"),focuscolor="yellow",highlightthickness=0)
        self.STYLE.configure("TButton.Frame",background="#6c09ed",borderwidth=2,relief=SOLID,foreground="black")
        self.STYLE.map("TButton",background=[("active","yellow"),("!active","#6c09ed")],foreground=[("active","#6c09ed"),("!active","yellow")])

        # scrollbars style
        self.STYLE.element_create("Horizontal.TScrollbar","from","clam")
        self.STYLE.element_create("Horizontal.TScrollbar.trough","from","classic")
        self.STYLE.element_create("Horizontal.TScrollbar.leftarrow","from","clam")
        self.STYLE.element_create("Horizontal.TScrollbar.rightarrow","from","clam")
        self.STYLE.element_create("Horizontal.TScrollbar.thumb","from","clam")
        self.STYLE.element_create("Horizontal.TScrollbar.grip","from","clam")
        self.STYLE.layout("Horizontal.TScrollbar",[('Horizontal.TScrollbar.trough', 
        {'sticky': 'we', 'children': [('Horizontal.TScrollbar.leftarrow', 
        {'side': 'left', 'sticky': ''}), ('Horizontal.TScrollbar.rightarrow', 
        {'side': 'right', 'sticky': ''}), ('Horizontal.TScrollbar.thumb', 
        {'sticky': 'nswe', 'unit': '1', 'children': [('Horizontal.TScrollbar.grip', 
        {'sticky': ''})]})]})])
        self.STYLE.configure("Horizontal.TScrollbar",troughborderwidth=2,thickness=0,gripcount=0,background="#00002c",borderwidth=0,relief=SOLID,lightcolor='black',darkcolor='black',troughcolor="white",arrowcolor="white")

        # vertical bar
        self.STYLE.element_create("Vertical.TScrollbar","from","alt")
        self.STYLE.element_create("Vertical.TScrollbar.trough","from","classic")
        self.STYLE.element_create("Vertical.TScrollbar.uparrow","from","clam")
        self.STYLE.element_create("Vertical.TScrollbar.downarrow","from","clam")
        self.STYLE.element_create("Vertical.TScrollbar.thumb","from","clam")
        self.STYLE.element_create("Vertical.TScrollbar.grip","from","clam")
        self.STYLE.layout("Vertical.TScrollbar",[('Vertical.TScrollbar.trough', 
        {'sticky': 'ns', 'children': [('Vertical.TScrollbar.uparrow', 
        {'side': 'top', 'sticky': ''}), ('Vertical.TScrollbar.downarrow', 
        {'side': 'bottom', 'sticky': ''}), ('Vertical.TScrollbar.thumb', 
        {'sticky': 'nswe', 'unit': '1', 'children': [('Vertical.TScrollbar.grip', 
        {'sticky': ''})]})]})])
        self.STYLE.configure("Vertical.TScrollbar",troughborderwidth=2,gripcount=0,background="#00002c",borderwidth=0,relief=SOLID,lightcolor='black',darkcolor='black',troughcolor="white",arrowcolor="white")
        self.STYLE.configure("TRadiobutton",background="#00002c",foreground="white",font=("arial",12,"bold"),borderwidth=0)
        self.STYLE.configure("TCheckbutton",background="#00002c",foreground="white",font=("arial",14,"bold"))
        self.STYLE.map("TRadiobutton",background=[("selected","yellow")],foreground=[("selected","black")])

        # Horizontal Scale
        self.STYLE.element_create("TScale","from","clam")
        self.STYLE.element_create("TScale.focus","from","clam")
        self.STYLE.element_create("TScale.trough","from","clam")
        self.STYLE.element_create("TScale.track","from","clam")
        self.STYLE.element_create("TScale.slider","from","clam")
        self.STYLE.layout("TScale",[('TScale.focus', {'expand': '1', 'sticky': 
        'nswe', 'children': [('Horizontal.TScale.trough', {'expand': '1', 
        'sticky': 'nswe', 'children': [('Horizontal.TScale.track', 
        {'sticky': 'we'}), ('Horizontal.TScale.slider', {'side': 'left', 
        'sticky': ''})]})]})])
        self.STYLE.configure("TScale",background="#00002c",troughcolor="red",foreground="red")

        # notebook
        self.STYLE.element_create("TNotebook","from","default")
        self.STYLE.element_create("TNotebook.tab","from","alt")
        self.STYLE.element_create("TNotebook.padding","from","default")
        self.STYLE.element_create("TNotebook.focus","from","clam")
        self.STYLE.element_create("TNotebook.label","from","default")
        self.STYLE.layout("TNotebook",[('Notebook.client', {'sticky': 'nswe'})])
        self.STYLE.layout("TNotebook.Tab",[('TNotebook.tab', {'sticky': 'nswe', 'children': 
        [('TNotebook.padding', {'side': 'top', 'sticky': 'nswe', 'children': 
        [('TNotebook.focus', {'side': 'top', 'sticky': 'nswe', 'children': 
        [('TNotebook.label', {'side': 'top', 'sticky': ''})]})]})]})])
        self.STYLE.configure("TNotebook",background="#6c09ed",highlightthickness=0,padding=(0,0,0,0),margin=(0,0,0,0),tabmargins=1)
        self.STYLE.configure("TNotebook.Tab",font=("Calibri",13),background="#00002c",foreground="yellow",borderwidth=1,shiftrelief=SOLID,relief=SOLID,padding=2,highlightthickness=0,margin=0,cursor="hand2")

        # Separator
        self.STYLE.element_create("TSeparator","from","default")
        self.STYLE.layout("TSeparator",[('Separator.separator', {'sticky': 'nswe'})])
        self.STYLE.configure("TSeparator",background="#6c09ed",padding=7)
        
        
        # Side Frame
        self.SideFrame=Frame(self.root,border=1,relief=SOLID,bg="#00002c")
        # Home Button
        self.Home_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="HOME",cursor="hand2",command=self.HOME_WIN_FUNC)
        self.Home_Button.grid(row=0,column=0,pady=2,padx=2,sticky="nswe")
        # Scan Button
        self.Scan_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="SCAN",cursor="hand2",state=DISABLED,command=self.SCAN_WIN_FUNC)
        self.Scan_Button.grid(row=1,column=0,pady=2,padx=2,sticky="nswe")
        # OCR Button
        self.OCR_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="OCR",cursor="hand2",state=DISABLED,command=self.OCR_WIN_FUNC)
        self.OCR_Button.grid(row=2,column=0,pady=2,padx=2,sticky="nswe")
        # Export Button
        self.Export_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="RECORDS",cursor="hand2",command=self.EXPORT_WIN_FUNC)
        self.Export_Button.grid(row=3,column=0,pady=2,padx=2,sticky="nswe")
        # Reset Button
        self.Reset_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="RESET",cursor="hand2",state=DISABLED,command=self.Reset_ALL_FUNC)
        self.Reset_Button.grid(row=4,column=0,pady=2,padx=2,sticky="nswe")
        # Setting Button
        self.Setting_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="SETTING",cursor="hand2",command=self.Setting_WIN_FUNC)
        self.Setting_Button.grid(row=5,column=0,pady=2,padx=2,sticky="nswe")
        # Help Button
        self.Help_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="HELP",cursor="hand2",command=self.Help_Window_FUNC)
        self.Help_Button.grid(row=6,column=0,pady=2,padx=2,sticky="nswe")
        # Keyboard Button
        self.KeyBoard_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="KEYBOARD\nSHORTCUT",cursor="hand2",command=self.Shortcut_Keys_Win_FUNC)
        self.KeyBoard_Button.grid(row=7,column=0,pady=2,padx=2,sticky="nswe")
        # PDF button
        self.PDF_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="PDF EDIT",cursor="hand2",command=self.PDF_WIN_FUNC)
        self.PDF_Button.grid(row=8,column=0,padx=2,pady=2,sticky="nswe")
        # exit button
        self.Exit_Button=Button(self.SideFrame,font=("Liberation Sans",10,"bold"),width=15,bg="#6c09ed",fg="yellow",disabledforeground="#082050",border=1,relief=SOLID,text="EXIT",cursor="hand2",command=self.Exit_FUNC)
        self.Exit_Button.grid(row=9,column=0,padx=2,pady=2,sticky="nswe")
        # Size pdf page
        self.Size_PDF_Page_Label=Label(self.SideFrame,bg="#00002c",fg="yellow",font=("arial",12,"bold"),anchor="nw")
        self.Size_PDF_Page_Label.grid(row=10,column=0,padx=2,pady=2,sticky="nswe")
        # magnifying glass
        self.Magnifying_Glass_Label=Label(self.SideFrame,border=0,relief=SOLID,bg="#00002c")
        self.Magnifying_Glass_Label.grid(row=11,column=0,padx=2,pady=2,sticky="nswe")
        
        self.SideFrame.grid(row=0,column=1,rowspan=2,padx=0,pady=0,sticky="nswe")
        # scroll bars
        self.Xbar=ttk.Scrollbar(self.root,orient=HORIZONTAL)
        self.Xbar.grid(row=1,column=0,padx=0,pady=0,sticky="nswe")

        self.Ybar=ttk.Scrollbar(self.root,orient=VERTICAL)
        self.Ybar.grid(row=0,column=2,rowspan=2,padx=0,pady=0,sticky="nswe")

        # ----------------------Home Window----------------------
        self.HomeBody=Frame(self.root,bg="#6c09ed",border=1,relief=SOLID)
        self.HomeBody.columnconfigure(0,weight=1)
        self.HomeBody.rowconfigure(2,weight=1)
        # label
        # Label(self.HomeBody,text="Document Scanner",font=("Calibri",30,"bold"),bg="#6c09ed",fg="yellow").grid(row=0,column=0,columnspan=8,pady=2,padx=2,sticky="nswe")
        # Buttons
        self.ImportImage_Button=Button(self.HomeBody,text=f"IMPORT",font=("Liberation Sans",10,"bold"),activebackground="#00002c",activeforeground="yellow",bg="yellow",border=1,relief=SOLID,cursor="hand2",command=self.ImportImage_FUNC)
        self.ImportImage_Button.grid(row=1,column=6,padx=2,pady=2,sticky="nswe")

        self.WebCam_Button=Button(self.HomeBody,text="WEBCAM",font=("Liberation Sans",10,"bold"),activebackground="#00002c",activeforeground="yellow",bg="yellow",border=1,relief=SOLID,cursor="hand2",command=self.Webcam_WIN_FUNC)
        self.WebCam_Button.grid(row=1,column=7,padx=2,pady=2,sticky="nswe")

        # scrollbar set canvas
        self.Home_Scrollbar_Canvas=Canvas(self.HomeBody)
        self.Home_Scrollbar_Canvas.grid(row=2,column=0,columnspan=9,pady=2,padx=2,sticky="nswe")
        # Main label
        self.MainLabel1=Label(self.HomeBody,text="Welcome to Document Scanner",fg="yellow",font=("arial",20),bg="#00002c",border=1,relief=SOLID)
        self.MainLabel1.grid(row=2,column=0,columnspan=9,pady=2,padx=2,sticky="nswe")
        self.HomeBody.grid(row=0,column=1,padx=0,pady=0,sticky="nswe")

        # ----------------------Scan Window----------------------
        self.ScanBody=Frame(self.root,bg="#6c09ed",border=1,relief=SOLID)
        self.ScanBody.rowconfigure(0,weight=1)
        self.ScanBody.columnconfigure(0,weight=1)
        # main canvas
        self.MainCanvas1=Canvas(self.ScanBody,border=0,relief=SOLID,highlightthickness=1,highlightbackground="yellow",highlightcolor="yellow",bg="#00002c")
        self.MainCanvas1.grid(row=0,column=0,padx=0,pady=0,sticky="nswe")
        # controls
        self.Controls=Frame(self.ScanBody,border=0,relief=SOLID,bg="#00002c",highlightthickness=1,highlightbackground="yellow",highlightcolor="yellow",padx=2,pady=2)
        for i in range(12):
            self.Controls.columnconfigure(i,weight=1)
        # export
        self.Export_PDF_Button=ttk.Button(self.Controls,text="Export PDF",cursor="hand2",command=self.Save_PDF_FUNC)
        self.Export_PDF_Button.grid(row=0,column=0,padx=2,pady=2,sticky="nswe")
        # Save Image
        self.Save_image_Button=ttk.Button(self.Controls,text="Export Image",cursor="hand2",command=self.Save_IMAGE_FUNC)
        self.Save_image_Button.grid(row=0,column=1,padx=2,pady=2,sticky="nswe")
        # Save Images
        self.Save_ADDimage_Button=ttk.Button(self.Controls,text="Export ADD List",cursor="hand2",command=self.Save_ADDLIST_FUNC_Thread)
        self.Save_ADDimage_Button.grid(row=0,column=2,padx=2,pady=2,sticky="nswe")
        # add to list image
        self.Add_List_Button=ttk.Button(self.Controls,text="ADD (➕)",cursor="hand2",command=self.Adding_Scan_Image_FUNC)
        self.Add_List_Button.grid(row=0,column=3,padx=2,pady=2,sticky="nswe")
        # Rotate Image
        self.Rotate_image_Button=ttk.Button(self.Controls,text="Rotate Left ↪",cursor="hand2",command=self.Rotation_image_Left)
        self.Rotate_image_Button.grid(row=0,column=4,padx=2,pady=2,sticky="nswe")
        # Scan for OCR Image
        self.OCR_ADD_Button=ttk.Button(self.Controls,text="Add to OCR",cursor="hand2",command=self.Adding_Scan_OCR_FUNC)
        self.OCR_ADD_Button.grid(row=0,column=5,padx=2,pady=2,sticky="nswe")
        # Pointer label
        self.Circle_Label=Label(self.Controls,bg="#00002c",fg="yellow",font=("arial",11))
        self.Circle_Label.grid(row=0,column=6,padx=2,pady=2,sticky="nswe")
        # List label
        self.List_ADDED_Label=Label(self.Controls,bg="#00002c",fg="lime",font=("arial",11))
        self.List_ADDED_Label.grid(row=0,column=7,padx=2,pady=2,sticky="nswe")
        # ZOOM IN Image
        self.ZOOMIN_Button=Button(self.Controls,text="➕🔍",font=("arial",11,"bold"),width=5,cursor="hand2",bg="#6c09ed",fg="yellow",border=0,activebackground="white",activeforeground="#6c09ed",command=self.Zoom_IN_FUNC)
        self.ZOOMIN_Button.grid(row=0,column=8,padx=2,pady=2,sticky="nswe")
        # ZOOM OUT Image
        self.ZOOMOUT_Button=Button(self.Controls,text="➖🔍",font=("arial",11,"bold"),width=5,cursor="hand2",bg="#6c09ed",fg="yellow",border=0,activebackground="white",activeforeground="#6c09ed",command=self.Zoom_OUT_FUNC)
        self.ZOOMOUT_Button.grid(row=0,column=9,padx=2,pady=2,sticky="nswe")
        # Edit List Image
        self.Edit_List_Button=ttk.Button(self.Controls,text="ADD List",cursor="hand2",command=self.Edit_LIST_WIN_FUNC)
        self.Edit_List_Button.grid(row=0,column=10,padx=2,pady=2,sticky="nswe")
        # Scan Image
        self.PreviewScan_Button=ttk.Button(self.Controls,text="Preview Scan",cursor="hand2",command=self.Preview_Scanning_FUNC)
        self.PreviewScan_Button.grid(row=0,column=11,padx=2,pady=2,sticky="nswe")
        # Scan Image
        self.Scan2PDF_Button=ttk.Button(self.Controls,text="Insert PDF",cursor="hand2",command=self.Scan2PDF_FUNC)
        self.Scan2PDF_Button.grid(row=0,column=12,padx=2,pady=2,sticky="nswe")
        
        self.Controls.grid(row=1,column=0,pady=0,padx=0,sticky="nswe")
        self.ScanBody.grid_forget()

        # ----------------------OCR Window----------------------
        self.OCRBody=Frame(self.root,bg="#6c09ed",border=1,relief=SOLID)
        self.OCRBody.rowconfigure(0,weight=1)
        self.OCRBody.columnconfigure(0,weight=1)
        # panel window
        self.Panels=PanedWindow(self.OCRBody,orient=HORIZONTAL,bg="yellow",border=0)

        self.MainLabel2=Label(self.Panels,bg="#00002c",border=1,relief=SOLID)
        self.MainLabel2.pack(fill=BOTH,expand=True)
        # text box
        self.OCR_TextBox=Text(self.Panels,font=("arial",12),bg="#00002c",fg="white",border=1,relief=SOLID,wrap=WORD,undo=True,insertbackground="red",selectbackground="yellow",selectforeground="#6c09ed")
        self.OCR_TextBox.pack(fill=BOTH,expand=True)

        self.P1=self.Panels.add(self.MainLabel2)
        self.P2=self.Panels.add(self.OCR_TextBox)
        self.Panels.paneconfigure(self.MainLabel2,width=int(self.OCRBody.winfo_screenwidth()/2))
        self.Panels.grid(row=0,column=0,pady=1,padx=1,sticky="nswe")

        # controls
        self.Controls_frame=Frame(self.OCRBody,border=1,relief=SOLID,bg="#00002c")
        # export words
        self.Export_Word_Button=ttk.Button(self.Controls_frame,text="Export",cursor="hand2",command=self.Save_OCR_Output)
        self.Export_Word_Button.grid(row=0,column=0,pady=2,padx=2,sticky="nswe")
        # OCR words
        self.Back_Scan_Button=ttk.Button(self.Controls_frame,text="Scan",cursor="hand2",command=self.SCAN_WIN_FUNC)
        self.Back_Scan_Button.grid(row=0,column=1,pady=2,padx=2,sticky="nswe")
        # OCR words
        self.OCR_WORK_Button=ttk.Button(self.Controls_frame,text="Run OCR",cursor="hand2",command=self.OCR_FUNC)
        self.OCR_WORK_Button.grid(row=0,column=2,pady=2,padx=2,sticky="nswe")

        self.Controls_frame.grid(row=1,column=0,padx=0,pady=0,sticky="nswe")
        self.OCRBody.grid_forget()

        # ----------------------Export Window----------------------
        self.ExportBody_Frame=Frame(self.root)
        self.ExportBody=Canvas(self.ExportBody_Frame,bg="#6c09ed",border=1,relief=SOLID,highlightthickness=0)
        self.Export_Frame=Frame(self.ExportBody,bg="#00002c",border=1,relief=SOLID)
        # label
        Label(self.Export_Frame,text="History",font=("arial",20,"bold"),bg="#00002c",fg="yellow",anchor="nw").grid(row=0,columnspan=4,column=0,padx=2,pady=2,sticky="nswe")
        self.Export_Frame.pack()
        self.ExportBody.create_window((0,0),window=self.Export_Frame,anchor="nw")
        self.ExportBody.pack(fill=BOTH,expand=True)
        self.ExportBody_Frame.grid_forget()

        # ----------------------PDF Edit Window----------------------
        self.PDF_EDIT_Body=Frame(self.root,bg="#6c09ed")
        self.PDF_EDIT_Body.columnconfigure(0,weight=1)
        self.PDF_EDIT_Body.rowconfigure(0,weight=1)
        # main label
        self.MainLabel_PDF=Label(self.PDF_EDIT_Body,bg="#00002c",text="PDF Edit will create a new pdf with some modification such as insert or Remove Page\n\nNote : The PDF Edit can take Huge Time for Loading and Processing\n Regarding the PDF File Size.\nIt may slow down the Performance Time.",fg="yellow",font=("arial",12))
        self.MainLabel_PDF.grid(row=0,column=0,padx=4,pady=4,sticky="nswe")

        # controls pdf
        self.Control_PDF_Frame=Frame(self.PDF_EDIT_Body,bg="#00002c",highlightthickness=1,highlightcolor="yellow",highlightbackground="yellow")
        for i in range(10):
            self.Control_PDF_Frame.columnconfigure(i,weight=1)
        # import button
        self.PDF_Edit_Import_Button=ttk.Button(self.Control_PDF_Frame,text="Import",cursor="hand2",command=self.Import_PDF_Thread_FUNC)
        self.PDF_Edit_Import_Button.grid(row=0,column=0,padx=2,pady=2,sticky="nswe")
        # Insert Image
        self.PDF_Edit_Insert_Button=ttk.Button(self.Control_PDF_Frame,text="Insert",cursor="hand2",command=self.Insert_PDF_FUNC)
        self.PDF_Edit_Insert_Button.grid(row=0,column=1,padx=2,pady=2,sticky="nswe")
        # Remove Image
        self.PDF_Edit_Remove_Button=ttk.Button(self.Control_PDF_Frame,text="Remove",cursor="hand2",command=self.Remove_PDF_FUNC)
        self.PDF_Edit_Remove_Button.grid(row=0,column=2,padx=2,pady=2,sticky="nswe")
        # Export Image
        self.PDF_Edit_Export_Image_Button=ttk.Button(self.Control_PDF_Frame,text="Export Image",cursor="hand2",command=self.Export_PDF_Image_EDIT_FUNC)
        self.PDF_Edit_Export_Image_Button.grid(row=0,column=3,padx=2,pady=2,sticky="nswe")
        # Export PDF
        self.PDF_Edit_Export_Button=ttk.Button(self.Control_PDF_Frame,text="Export PDF",cursor="hand2",command=self.Export_PDF_EDIT_FUNC)
        self.PDF_Edit_Export_Button.grid(row=0,column=4,padx=2,pady=2,sticky="nswe")
        # Reset PDF
        self.PDF_Edit_Reset_Button=ttk.Button(self.Control_PDF_Frame,text="Reset PDF",cursor="hand2",command=self.Reset_PDF_FUNC)
        self.PDF_Edit_Reset_Button.grid(row=0,column=5,padx=2,pady=2,sticky="nswe")

        # Previous Pdf Image
        self.Previous_PDF_Button=ttk.Button(self.Control_PDF_Frame,text="◀ Previous",cursor="hand2",command=self.Previous_PDF_FUNC)
        self.Previous_PDF_Button.grid(row=0,column=6,padx=2,pady=2,sticky="nswe")

        # Next Pdf Image
        self.Next_PDF_Button=ttk.Button(self.Control_PDF_Frame,text="Next ▶",cursor="hand2",command=self.Next_PDF_FUNC)
        self.Next_PDF_Button.grid(row=0,column=7,padx=2,pady=2,sticky="nswe")

        # list Pdf Image
        self.List_PDF_Save_Button=ttk.Button(self.Control_PDF_Frame,text="Export PDF LIST",cursor="hand2",command=self.Export_PDF_EDIT_LIST_Thread_FUNC)
        self.List_PDF_Save_Button.grid(row=0,column=8,padx=2,pady=2,sticky="nswe")

        # current pdf page
        self.Current_PDF_Page_Label=Label(self.Control_PDF_Frame,bg="#00002c",fg="yellow",font=("arial",12,"bold"))
        self.Current_PDF_Page_Label.grid(row=0,column=10,padx=2,pady=2,sticky="nswe")

        # Total pdf page
        self.Total_PDF_Page_Label=Label(self.Control_PDF_Frame,bg="#00002c",fg="yellow",font=("arial",12,"bold"))
        self.Total_PDF_Page_Label.grid(row=0,column=11,padx=2,pady=2,sticky="nswe")

        ttk.Button(self.Control_PDF_Frame,text="Rotate ↪",cursor="hand2",command=self.Rotate_PDF_IMAGE_FUNC).grid(row=0,column=12,padx=2,pady=2,sticky="nswe")

        self.Control_PDF_Frame.grid(row=1,column=0,padx=4,pady=4,sticky="nswe")
        self.PDF_EDIT_Body.grid_forget()

        self.MainCanvas1.bind("<B1-Motion>",self.Change_Points)
        self.MainCanvas1.bind("<ButtonRelease-1>",self.Change_mouse_Normal)
        self.root.bind("<Control-o>",self.ImportImage_FUNC)
        self.root.bind("<Control-s>",self.Setting_WIN_FUNC)
        self.root.bind("<Control-k>",self.Shortcut_Keys_Win_FUNC)
        self.root.bind("<Control-P>",self.PDF_WIN_FUNC)
        self.root.bind("<F5>",self.FullScreen_Keyboard_FUNC)
        self.HOME_WIN_FUNC()
        self.root.mainloop()
        pass

    #||||||||||||||||||||||||||||| To Change the Window |||||||||||||||||||||||||||||

    #----------To Open The Home Window----------
    def HOME_WIN_FUNC(self,*args):
        self.Home_Button.config(bg="yellow",fg="#6c09ed")
        self.Scan_Button.config(bg="#6c09ed",fg="yellow")
        self.OCR_Button.config(bg="#6c09ed",fg="yellow")
        self.Reset_Button.config(bg="#6c09ed",fg="yellow")
        self.Export_Button.config(bg="#6c09ed",fg="yellow")
        self.PDF_Button.config(bg="#6c09ed",fg="yellow")
        self.Home_Active=True

        if self.Home_Active==True:
            self.HomeBody.grid(row=0,column=0,padx=0,pady=0,sticky="nswe")
            self.Home_Scrollbar_Canvas.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set)
            self.Xbar.config(command=self.Home_Scrollbar_Canvas.xview)
            self.Ybar.config(command=self.Home_Scrollbar_Canvas.yview)

        if self.SCAN_Active==True:
            self.ScanBody.grid_forget()
            self.SCAN_Active=False

        if self.OCR_Active==True:
            self.OCRBody.grid_forget()
            self.OCR_Active=False

        if self.Export_Active==True:
            self.ExportBody_Frame.grid_forget()
            self.Export_Active=False

        if self.PDF_Active==True:
            self.PDF_EDIT_Body.grid_forget()
            self.PDF_Active=False
        pass

    #----------To Open The Scan Window----------
    def SCAN_WIN_FUNC(self,*args):
        self.Scan_Button.config(bg="yellow",fg="#6c09ed")
        self.Home_Button.config(bg="#6c09ed",fg="yellow")
        self.OCR_Button.config(bg="#6c09ed",fg="yellow")
        self.Reset_Button.config(bg="#6c09ed",fg="yellow")
        self.Export_Button.config(bg="#6c09ed",fg="yellow")
        self.PDF_Button.config(bg="#6c09ed",fg="yellow")
        self.SCAN_Active=True
        if self.Home_Active==True:
            self.HomeBody.grid_forget()
            self.Home_Active=False

        if self.SCAN_Active==True:
            self.ScanBody.grid(row=0,column=0,pady=0,padx=0,sticky="nswe")
            self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
            self.Xbar.config(command=self.MainCanvas1.xview)
            self.Ybar.config(command=self.MainCanvas1.yview)
            self.MainCanvas1.yview_moveto(0.0)
            self.MainCanvas1.xview_moveto(0.0)
            self.root.bind("<Control-Key-plus>",self.Zoom_IN_FUNC)
            self.root.bind("<Control-Key-minus>",self.Zoom_OUT_FUNC)
            self.root.bind("<Left>",self.Previous_FUNC)
            self.root.bind("<Right>",self.Next_FUNC)
            self.root.bind("<Control-w>",self.Rotation_image_Left)
            self.root.bind("<Control-a>",self.Adding_Scan_Image_FUNC)
            self.MainCanvas1.bind("<MouseWheel>",self.Scroll_Canvas1_FUNC)
            self.root.bind("<Control-t>",self.Adding_Scan_OCR_FUNC)
            self.root.bind("<Control-p>",self.Preview_Scanning_FUNC)
            pass

        if self.OCR_Active==True:
            self.OCRBody.grid_forget()
            self.OCR_Active=False

        if self.Export_Active==True:
            self.ExportBody_Frame.grid_forget()
            self.Export_Active=False

        if self.PDF_Active==True:
            self.PDF_EDIT_Body.grid_forget()
            self.PDF_Active=False
        pass

    #----------Use Mouse wheel to Scroll the canvas----------
    def Scroll_Canvas1_FUNC(self,e):
        self.MainCanvas1.yview_scroll(int(-1*(e.delta/120)), "units")
        pass

    #----------To Open The OCR Window----------
    def OCR_WIN_FUNC(self,*args):
        self.OCR_Button.config(bg="yellow",fg="#6c09ed")
        self.Home_Button.config(bg="#6c09ed",fg="yellow")
        self.Scan_Button.config(bg="#6c09ed",fg="yellow")
        self.Reset_Button.config(bg="#6c09ed",fg="yellow")
        self.Export_Button.config(bg="#6c09ed",fg="yellow")
        self.PDF_Button.config(bg="#6c09ed",fg="yellow")
        self.OCR_Active=True
        if self.Home_Active==True:
            self.HomeBody.grid_forget()
            self.Home_Active=False

        if self.SCAN_Active==True:
            self.ScanBody.grid_forget()
            self.SCAN_Active=False

        if self.OCR_Active==True:
            self.OCR_TextBox.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set)
            self.Xbar.config(command=self.OCR_TextBox.xview)
            self.Ybar.config(command=self.OCR_TextBox.yview)
            self.OCRBody.grid(row=0,column=0,padx=0,pady=0,sticky="nswe")
            self.root.bind("<F1>",self.OCR_FUNC)

        if self.Export_Active==True:
            self.ExportBody_Frame.grid_forget()
            self.Export_Active=False

        if self.PDF_Active==True:
            self.PDF_EDIT_Body.grid_forget()
            self.PDF_Active=False
        pass

    #----------To Open The Export Window----------
    def EXPORT_WIN_FUNC(self,*args):
        self.Export_Button.config(bg="yellow",fg="#6c09ed")
        self.Home_Button.config(bg="#6c09ed",fg="yellow")
        self.Scan_Button.config(bg="#6c09ed",fg="yellow")
        self.Reset_Button.config(bg="#6c09ed",fg="yellow")
        self.OCR_Button.config(bg="#6c09ed",fg="yellow")
        self.PDF_Button.config(bg="#6c09ed",fg="yellow")
        self.Export_Active=True
        if self.Home_Active==True:
            self.HomeBody.grid_forget()
            self.Home_Active=False

        if self.SCAN_Active==True:
            self.ScanBody.grid_forget()
            self.SCAN_Active=False

        if self.OCR_Active==True:
            self.OCRBody.grid_forget()
            self.OCR_Active=False

        if self.PDF_Active==True:
            self.PDF_EDIT_Body.grid_forget()
            self.PDF_Active=False

        if self.Export_Active==True:
            self.ExportBody_Frame.grid(row=0,column=0,padx=0,pady=0,sticky="nswe")
            os.chdir(self.DataBase_DIR)
            if os.path.isfile(self.DataBase_FILE):
                conn=sqlite3.connect(self.DataBase_FILE)
                datas=conn.execute(f'''SELECT * FROM {self.Data_TABLE}''')
                for d in self.Export_Frame.winfo_children():
                    d.destroy()
                Label(self.Export_Frame,text="History",font=("arial",20,"bold"),bg="#00002c",fg="yellow",anchor="nw").grid(row=0,columnspan=4,column=0,padx=2,pady=2,sticky="nswe")
                Label(self.Export_Frame,text=f"{self.DataBase_FILE}",font=("arial",15,"bold"),bg="#00002c",fg="yellow",anchor="nw").grid(row=1,column=0,columnspan=4,padx=2,pady=2,sticky="nswe")
                Label(self.Export_Frame,text="Sr No.",font=("arial",12,"bold"),bg="#4d00aa",fg="yellow",border=1,relief=SOLID,padx=10,pady=10).grid(row=2,column=0,pady=5,padx=2,sticky="nswe")
                Label(self.Export_Frame,text="File Name",font=("arial",12,"bold"),bg="#4d00aa",fg="yellow",border=1,relief=SOLID,padx=10,pady=10).grid(row=2,column=1,pady=5,padx=2,sticky="nswe")
                Label(self.Export_Frame,text="File Path",font=("arial",12,"bold"),bg="#4d00aa",fg="yellow",border=1,relief=SOLID,padx=10,pady=10).grid(row=2,column=2,pady=5,padx=2,sticky="nswe")
                Label(self.Export_Frame,text="File Format",font=("arial",12,"bold"),bg="#4d00aa",fg="yellow",border=1,relief=SOLID,padx=10,pady=10).grid(row=2,column=3,pady=5,padx=2,sticky="nswe")
                Label(self.Export_Frame,text="Date and Time",font=("arial",12,"bold"),bg="#4d00aa",fg="yellow",border=1,relief=SOLID,padx=10,pady=10).grid(row=2,column=4,pady=5,padx=2,sticky="nswe")
                Label(self.Export_Frame,text="Backup Path",font=("arial",12,"bold"),bg="#4d00aa",fg="yellow",border=1,relief=SOLID,padx=10,pady=10).grid(row=2,column=5,pady=5,padx=2,sticky="nswe")
                for index,i in enumerate(datas):
                    Label(self.Export_Frame,text=index+1,font=("Calibri",12,"bold"),bg="#6c09ed",fg="yellow",border=1,relief=SOLID,padx=10,pady=10).grid(row=index+3,column=0,pady=5,padx=2,sticky="nswe")
                    Label(self.Export_Frame,text=i[0],font=("Calibri",12,"bold"),bg="#071d54",fg="white",border=1,relief=SOLID,padx=10,pady=10).grid(row=index+3,column=1,pady=5,padx=2,sticky="nswe")
                    Label(self.Export_Frame,text=i[1],font=("Calibri",12,"bold"),bg="#071d54",fg="white",border=1,relief=SOLID,padx=10,pady=10).grid(row=index+3,column=2,pady=5,padx=2,sticky="nswe")
                    Label(self.Export_Frame,text=i[2],font=("Calibri",12,"bold"),bg="#071d54",fg="white",border=1,relief=SOLID,padx=10,pady=10).grid(row=index+3,column=3,pady=5,padx=2,sticky="nswe")
                    Label(self.Export_Frame,text=i[3],font=("Calibri",12,"bold"),bg="#071d54",fg="white",border=1,relief=SOLID,padx=10,pady=10).grid(row=index+3,column=4,pady=5,padx=2,sticky="nswe")
                    Label(self.Export_Frame,text=i[4],font=("Calibri",12,"bold"),bg="#071d54",fg="white",border=1,relief=SOLID,padx=10,pady=10).grid(row=index+3,column=5,pady=5,padx=2,sticky="nswe")
                self.ExportBody.bind("<MouseWheel>",self.Scroll_Canvas2_FUNC)
                self.Export_Frame.bind("<MouseWheel>",self.Scroll_Canvas2_FUNC)
                self.Xbar.config(command=self.ExportBody.xview)
                self.Ybar.config(command=self.ExportBody.yview)
                self.ExportBody.config(scrollregion=self.ExportBody.bbox(ALL),xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set)
            else:
                for d in self.Export_Frame.winfo_children():
                    d.destroy()
                Label(self.Export_Frame,text="Error or There is no Record",font=("arial",12),bg="#6c09ed",fg="white",padx=20,pady=20).grid(row=1,column=0)
            self.ExportBody.bind("<MouseWheel>",self.Scroll_Canvas2_FUNC)
            self.Export_Frame.bind("<MouseWheel>",self.Scroll_Canvas2_FUNC)
            self.ExportBody.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.ExportBody.bbox(ALL))
            self.Xbar.config(command=self.ExportBody.xview)
            self.Ybar.config(command=self.ExportBody.yview)
        pass

    #----------To Open The PDF Export Window----------
    def PDF_WIN_FUNC(self,*args):
        self.PDF_Button.config(bg="yellow",fg="#6c09ed")
        self.Export_Button.config(bg="#6c09ed",fg="yellow")
        self.Home_Button.config(bg="#6c09ed",fg="yellow")
        self.Scan_Button.config(bg="#6c09ed",fg="yellow")
        self.Reset_Button.config(bg="#6c09ed",fg="yellow")
        self.OCR_Button.config(bg="#6c09ed",fg="yellow")
        self.PDF_Active=True
        if self.Home_Active==True:
            self.HomeBody.grid_forget()
            self.Home_Active=False

        if self.SCAN_Active==True:
            self.ScanBody.grid_forget()
            self.SCAN_Active=False

        if self.OCR_Active==True:
            self.OCRBody.grid_forget()
            self.OCR_Active=False

        if self.Export_Active==True:
            self.ExportBody_Frame.grid_forget()
            self.Export_Active=False

        if self.PDF_Active==True:
            self.PDF_EDIT_Body.grid(row=0,column=0,padx=0,pady=0,sticky="nswe")
            self.root.bind("<Left>",self.Previous_PDF_FUNC)
            self.root.bind("<Right>",self.Next_PDF_FUNC)
        pass
    
    #----------Use Mouse wheel to Scroll the canvas----------
    def Scroll_Canvas2_FUNC(self,e):
        self.ExportBody.yview_scroll(int(-1*(e.delta/120)), "units")
        pass

    #----------Display the Status Function----------
    def Display_Status_FUNC(self,*args):
        self.Status_Active=True
        self.Home_Button.config(state=NORMAL,bg="yellow",fg="#6c09ed")
        self.Scan_Button.config(state=NORMAL)
        self.OCR_Button.config(state=NORMAL)
        self.Export_Button.config(state=NORMAL)
        self.Reset_Button.config(state=NORMAL)
        # status bar
        self.StatusFrame=Frame(self.root,border=1,relief=SOLID,bg="#00002c")
        self.StatusFrame.columnconfigure(3,weight=1)
        # previous button
        self.Previous_Button=ttk.Button(self.StatusFrame,text="◀ PREVIOUS",cursor="hand2",command=self.Previous_FUNC)
        self.Previous_Button.grid(row=0,column=0,padx=2,pady=2,sticky="nswe")
        # Next button
        self.Next_Button=ttk.Button(self.StatusFrame,text="NEXT ▶",cursor="hand2",command=self.Next_FUNC)
        self.Next_Button.grid(row=0,column=1,padx=2,pady=2,sticky="nswe")
        # total number of image
        self.Total_Label=Label(self.StatusFrame,text="Total Page",bg="#00002c",fg="yellow",font=("arial",11))
        self.Total_Label.grid(row=0,column=2,pady=2,padx=2,sticky="nswe")
        # combobox
        self.List_image=StringVar()
        self.ListBox_Combo=ttk.Combobox(self.StatusFrame,textvariable=self.List_image,state="readonly",font=("Liberation Sans",11,"bold"))
        self.ListBox_Combo.grid(row=0,column=3,padx=2,pady=2,sticky="nswe")
        self.ListBox_Combo["value"]=args[0]
        self.ListBox_Combo.bind("<<ComboboxSelected>>",self.Combobox_Change_FUNC)
        # display side tools
        self.Display_Side_Tools_Button = ttk.Button(self.StatusFrame,text="☰",cursor="hand2",command=self.Show_Hide_Tools_FUNC)
        self.Display_Side_Tools_Button.grid(row=0,column=4,padx=2,pady=2,sticky="nswe")
        self.StatusFrame.grid(row=2,column=0,columnspan=3,pady=0,padx=0,sticky="nswe")

        self.Total_Label.config(text=f"Total Page = 1 / {len(self.Org_List)}")

        self.root.bind("<Control-S>",self.SCAN_WIN_FUNC)
        self.root.bind("<Control-H>",self.HOME_WIN_FUNC)
        self.root.bind("<Control-O>",self.OCR_WIN_FUNC)
        self.root.bind("<Control-R>",self.EXPORT_WIN_FUNC)
        self.root.bind("<Left>",self.Previous_FUNC)
        self.root.bind("<Right>",self.Next_FUNC)
        pass

    #----------Show or Hide the Side Tools----------
    def Show_Hide_Tools_FUNC(self,*args):
        if len(self.Org_List):
            if self.SideTOOL_Active == True:
                self.SideFrame.grid_forget()
                self.SideTOOL_Active = False
            elif self.SideTOOL_Active == False:
                self.SideFrame.grid(row=0,column=1,rowspan=2,padx=0,pady=0,sticky="nswe")
                self.SideTOOL_Active = True
        else:
            msgbox.showwarning("Warning","This Feature will only work when there are image/images loaded ")
        pass

    #||||||||||||||||||||||||||||| Main Functions |||||||||||||||||||||||||||||

    #----------For Importing the Images----------
    def ImportImage_FUNC(self,*args):
        files=filedialog.askopenfilenames(title="Import Images")
        if files=="":
            pass
        else:
            for i in files:
                if os.path.splitext(os.path.basename(i))[1].lower() in self.IMG_FORMAT and i not in self.Org_List:
                    self.Org_List.append(i)
            if self.Org_List!=[]:
                if self.Status_Active==False:
                    self.Display_Status_FUNC(self.Org_List)
                    self.Status_Active=True
                elif self.Status_Active==True:
                    self.ListBox_Combo["values"]=self.Org_List
                    dataindex=self.ListBox_Combo.current()
                    self.Total_Label.config(text=f"Total Page = 1 / {len(self.Org_List)}")
                    pass
                self.ListBox_Combo.set(self.Org_List[0])
                data=self.ListBox_Combo.get()

                self.root.title(f"{self.title} - {os.path.basename(data)}")

                img=Image.open(data)
                LH,LW=int(self.MainLabel1.winfo_height()-60),int(self.MainLabel1.winfo_width()-60)
                self.Thumbnail_Range=(LW,LH)
                img.thumbnail(self.Thumbnail_Range,Image.ANTIALIAS)
                img=ImageTk.PhotoImage(image=img)
                self.MainLabel1.config(image=img)
                self.MainLabel1.image=img
                    
                # canvas image
                imgc=Image.open(data)
                self.MainCanvas1.delete(ALL)
                # import image in canvas
                self.opencvImage=cv2.resize(np.array(imgc),(0, 0), fx = self.fixed_ratio, fy = self.fixed_ratio,interpolation=cv2.INTER_LANCZOS4)
                self.image=Image.fromarray(self.opencvImage)
                    
                W,H=self.opencvImage.shape[1],self.opencvImage.shape[0]
                self.Image_Height=H
                self.Image_Width=W
                    
                imgtk=ImageTk.PhotoImage(image=self.image)
                self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
                self.MainCanvas1.image=imgtk
                # polygon
                # auto scan
                conts=self.Auto_Scan_FUNC(self.opencvImage)
                if conts and self.Auto_Scan_Active==True:
                    biggest=conts[0][0]
                    self.C1=list(self.ReOrder_FUNC(biggest)[0][0])
                    self.C2=list(self.ReOrder_FUNC(biggest)[1][0])
                    self.C3=list(self.ReOrder_FUNC(biggest)[2][0])
                    self.C4=list(self.ReOrder_FUNC(biggest)[3][0])
                else:
                    self.C1=[0,0]
                    self.C2=[int(W),0]
                    self.C3=[int(W),int(H)]
                    self.C4=[0,int(H)]
                    
                self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)

                self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],self.Circle_Radius,self.MainCanvas1,"red")
            else:
                msgbox.showerror("Error","There are no Images found or the image does not support the software")
        pass

    #----------Next Button Function----------
    def Next_FUNC(self,*args):
        x=self.ListBox_Combo.current()
        n=len(self.Org_List)
        count=x+1
        self.root.focus()
        if count<n:
            self.Total_Label.config(text=f"Total Page = {count+1} / {len(self.Org_List)}")

            self.ListBox_Combo.set(self.Org_List[count])
            data=self.ListBox_Combo.get()
            dataindex=self.ListBox_Combo.current()
            if os.path.isfile(data):

                self.root.title(f"{self.title} - {os.path.basename(data)}")
                self.fixed_ratio=self.Constant_Size
                self.Size_Ratio=0.1
                self.Rotate_Point=0
                self.Magnifying_Glass_Label.config(image="")
                self.Circle_Label.config(text="")

                img=Image.open(data)
                img.thumbnail(self.Thumbnail_Range,Image.ANTIALIAS)
                img=ImageTk.PhotoImage(image=img)
                self.MainLabel1.config(image=img)
                self.MainLabel1.image=img
                
                imgc=Image.open(data)
                self.MainCanvas1.delete(ALL)
                # import image in canvas
                self.opencvImage=cv2.resize(np.array(imgc),(0, 0), fx = self.fixed_ratio, fy = self.fixed_ratio,interpolation=cv2.INTER_LANCZOS4)
                self.image=Image.fromarray(self.opencvImage)
                        
                W,H=self.opencvImage.shape[1],self.opencvImage.shape[0]
                self.Image_Height=H
                self.Image_Width=W
                        
                imgtk=ImageTk.PhotoImage(image=self.image)
                self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
                self.MainCanvas1.image=imgtk
                # polygon
                # auto scan
                conts=self.Auto_Scan_FUNC(self.opencvImage)
                if conts and self.Auto_Scan_Active==True:
                    biggest=conts[0][0]
                    self.C1=list(self.ReOrder_FUNC(biggest)[0][0])
                    self.C2=list(self.ReOrder_FUNC(biggest)[1][0])
                    self.C3=list(self.ReOrder_FUNC(biggest)[2][0])
                    self.C4=list(self.ReOrder_FUNC(biggest)[3][0])
                else:
                    self.C1=[0,0]
                    self.C2=[int(W),0]
                    self.C3=[int(W),int(H)]
                    self.C4=[0,int(H)]
                        
                self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)

                self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],self.Circle_Radius,self.MainCanvas1,"red")
                if self.SCAN_Active==True:
                    self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
                    self.Xbar.config(command=self.MainCanvas1.xview)
                    self.Ybar.config(command=self.MainCanvas1.yview)
                    self.MainCanvas1.yview_moveto(0.0)
                    self.MainCanvas1.xview_moveto(0.0)
            else:
                msgbox.showwarning("warning",f"The {data} \nhas been deleted/Moved")
        pass

    #----------Previous Button Function----------
    def Previous_FUNC(self,*args):
        x=self.ListBox_Combo.current()
        n=len(self.Org_List)
        count=x-1
        self.root.focus()
        if count>=0:
            self.Total_Label.config(text=f"Total Page = {count+1} / {len(self.Org_List)}")

            self.ListBox_Combo.set(self.Org_List[count])
            data=self.ListBox_Combo.get()
            dataindex=self.ListBox_Combo.current()
            if os.path.isfile(data):

                self.root.title(f"{self.title} - {os.path.basename(data)}")
                self.fixed_ratio=self.Constant_Size
                self.Size_Ratio=0.1
                self.Rotate_Point=0
                self.Magnifying_Glass_Label.config(image="")
                self.Circle_Label.config(text="")

                
                img=Image.open(data)
                img.thumbnail(self.Thumbnail_Range,Image.ANTIALIAS)
                img=ImageTk.PhotoImage(image=img)
                self.MainLabel1.config(image=img)
                self.MainLabel1.image=img
            
                imgc=Image.open(data)
                self.MainCanvas1.delete(ALL)
                # import image in canvas
                self.opencvImage=cv2.resize(np.array(imgc),(0, 0), fx = self.fixed_ratio, fy = self.fixed_ratio,interpolation=cv2.INTER_LANCZOS4)
                self.image=Image.fromarray(self.opencvImage)
                    
                W,H=self.opencvImage.shape[1],self.opencvImage.shape[0]
                self.Image_Height=H
                self.Image_Width=W
                    
                imgtk=ImageTk.PhotoImage(image=self.image)
                self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
                self.MainCanvas1.image=imgtk
                # polygon
                # auto scan
                conts=self.Auto_Scan_FUNC(self.opencvImage)
                if conts and self.Auto_Scan_Active==True:
                    biggest=conts[0][0]
                    self.C1=list(self.ReOrder_FUNC(biggest)[0][0])
                    self.C2=list(self.ReOrder_FUNC(biggest)[1][0])
                    self.C3=list(self.ReOrder_FUNC(biggest)[2][0])
                    self.C4=list(self.ReOrder_FUNC(biggest)[3][0])
                else:
                    self.C1=[0,0]
                    self.C2=[int(W),0]
                    self.C3=[int(W),int(H)]
                    self.C4=[0,int(H)]
                    
                self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)
                self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],self.Circle_Radius,self.MainCanvas1,"red")
                if self.SCAN_Active==True:
                    self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
                    self.Xbar.config(command=self.MainCanvas1.xview)
                    self.Ybar.config(command=self.MainCanvas1.yview)
                    self.MainCanvas1.xview_moveto(0.0)
                    self.MainCanvas1.yview_moveto(0.0)
            else:
                msgbox.showwarning("warning",f"The {data} \nhas been deleted/Moved")
        pass

    #----------Combobox change Function----------
    def Combobox_Change_FUNC(self,*args):
        dataindex=self.ListBox_Combo.current()
        self.Total_Label.config(text=f"Total Page = {dataindex+1} / {len(self.Org_List)}")

        self.ListBox_Combo.set(self.Org_List[dataindex])
        data=self.ListBox_Combo.get()
        self.root.focus()
        if os.path.isfile(data):

            self.root.title(f"{self.title} - {os.path.basename(data)}")
            self.fixed_ratio=self.Constant_Size
            self.Size_Ratio=0.1
            self.Rotate_Point=0

            img=Image.open(data)
            img.thumbnail(self.Thumbnail_Range,Image.ANTIALIAS)
            img=ImageTk.PhotoImage(image=img)
            self.MainLabel1.config(image=img)
            self.MainLabel1.image=img
        
            imgc=Image.open(data)
            self.MainCanvas1.delete(ALL)
            # import image in canvas
            self.opencvImage=cv2.resize(np.array(imgc),(0, 0), fx = self.fixed_ratio, fy = self.fixed_ratio,interpolation=cv2.INTER_LANCZOS4)
            self.image=Image.fromarray(self.opencvImage)
                
            W,H=self.opencvImage.shape[1],self.opencvImage.shape[0]
            self.Image_Height=H
            self.Image_Width=W
                    
            imgtk=ImageTk.PhotoImage(image=self.image)
            self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
            self.MainCanvas1.image=imgtk
            # polygon
            # auto scan
            conts=self.Auto_Scan_FUNC(self.opencvImage)
            if conts and self.Auto_Scan_Active==True:
                biggest=conts[0][0]
                self.C1=list(self.ReOrder_FUNC(biggest)[0][0])
                self.C2=list(self.ReOrder_FUNC(biggest)[1][0])
                self.C3=list(self.ReOrder_FUNC(biggest)[2][0])
                self.C4=list(self.ReOrder_FUNC(biggest)[3][0])
            else:
                self.C1=[0,0]
                self.C2=[int(W),0]
                self.C3=[int(W),int(H)]
                self.C4=[0,int(H)]
                    
            self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)
            self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],self.Circle_Radius,self.MainCanvas1,"red")
            self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],self.Circle_Radius,self.MainCanvas1,"red")
            self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],self.Circle_Radius,self.MainCanvas1,"red")
            self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],self.Circle_Radius,self.MainCanvas1,"red")
            if self.SCAN_Active==True:
                self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
                self.Xbar.config(command=self.MainCanvas1.xview)
                self.Ybar.config(command=self.MainCanvas1.yview)
                self.MainCanvas1.yview_moveto(0.0)
                self.MainCanvas1.xview_moveto(0.0)
        else:
            msgbox.showwarning("warning",f"The {data} \nhas been deleted/Moved")
        pass

    #----------Zoom in Function----------
    def Zoom_IN_FUNC(self,*args):
        if self.SCAN_Active==True and self.C1_cirlce in self.MainCanvas1.find_all():
            dataindex=self.ListBox_Combo.current()
            self.Total_Label.config(text=f"Total Page = {dataindex+1} / {len(self.Org_List)}")

            self.ListBox_Combo.set(self.Org_List[dataindex])
            data=self.ListBox_Combo.get()
            if os.path.isfile(data):

                self.root.title(f"{self.title} - {os.path.basename(data)}")

                imgc=Image.open(data)
                imgc=imgc.rotate(self.ROTATION_List[self.Rotate_Point],Image.ANTIALIAS,expand=1)
                self.MainCanvas1.delete(ALL)
                # import image in canvas
                self.fixed_ratio+=self.Size_Ratio
                if self.Constant_size_Active==True:
                    self.Constant_Size=self.fixed_ratio
                self.opencvImage=cv2.resize(np.array(imgc),(0, 0), fx = self.fixed_ratio, fy = self.fixed_ratio,interpolation=cv2.INTER_LANCZOS4)
                self.image=Image.fromarray(self.opencvImage)
                        
                W,H=self.opencvImage.shape[1],self.opencvImage.shape[0]
                self.Image_Height=H
                self.Image_Width=W
                        
                imgtk=ImageTk.PhotoImage(image=self.image)
                self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
                self.MainCanvas1.image=imgtk
                # polygon
                # auto scan
                conts=self.Auto_Scan_FUNC(self.opencvImage)
                if conts and self.Auto_Scan_Active==True:
                    biggest=conts[0][0]
                    self.C1=list(self.ReOrder_FUNC(biggest)[0][0])
                    self.C2=list(self.ReOrder_FUNC(biggest)[1][0])
                    self.C3=list(self.ReOrder_FUNC(biggest)[2][0])
                    self.C4=list(self.ReOrder_FUNC(biggest)[3][0])
                else:
                    self.C1=[0,0]
                    self.C2=[int(W),0]
                    self.C3=[int(W),int(H)]
                    self.C4=[0,int(H)]
                        
                self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)

                self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],self.Circle_Radius,self.MainCanvas1,"red")
                self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
                self.Xbar.config(command=self.MainCanvas1.xview)
                self.Ybar.config(command=self.MainCanvas1.yview)
                self.MainCanvas1.yview_moveto(0.0)
                self.MainCanvas1.xview_moveto(0.0)
            else:
                msgbox.showwarning("warning",f"The {data} \nhas been deleted/Moved")
        else:
            msgbox.showerror("Error","There is no Image")
        pass

    #----------Zoom out Function----------
    def Zoom_OUT_FUNC(self,*args):
        if self.SCAN_Active==True and self.C1_cirlce in self.MainCanvas1.find_all():
            dataindex=self.ListBox_Combo.current()
            self.Total_Label.config(text=f"Total Page = {dataindex+1} / {len(self.Org_List)}")

            self.ListBox_Combo.set(self.Org_List[dataindex])
            data=self.ListBox_Combo.get()
            if os.path.isfile(data):

                self.root.title(f"{self.title} - {os.path.basename(data)}")

                imgc=Image.open(data)
                imgc=imgc.rotate(self.ROTATION_List[self.Rotate_Point],Image.ANTIALIAS,expand=1)
                # import image in canvas
                x=self.fixed_ratio
                y=self.fixed_ratio
                y-=self.Size_Ratio
                if y>0 and self.image.size[0]>100 and self.image.size[1]>100:
                    self.fixed_ratio=y
                    if self.Constant_size_Active==True:
                        self.Constant_Size=self.fixed_ratio
                    try:
                        self.opencvImage=cv2.resize(np.array(imgc),(0, 0), fx = self.fixed_ratio, fy = self.fixed_ratio,interpolation=cv2.INTER_LANCZOS4)
                    except:
                        self.opencvImage=cv2.resize(np.array(imgc),(0, 0), fx = 0.01, fy = 0.01,interpolation=cv2.INTER_LANCZOS4)
                    self.image=Image.fromarray(self.opencvImage)
                    self.MainCanvas1.delete(ALL)  
                    W,H=self.opencvImage.shape[1],self.opencvImage.shape[0]
                    self.Image_Height=H
                    self.Image_Width=W
                            
                    imgtk=ImageTk.PhotoImage(image=self.image)
                    self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
                    self.MainCanvas1.image=imgtk
                    # polygon
                    # auto scan
                    conts=self.Auto_Scan_FUNC(self.opencvImage)
                    if conts and self.Auto_Scan_Active==True:
                        biggest=conts[0][0]
                        self.C1=list(self.ReOrder_FUNC(biggest)[0][0])
                        self.C2=list(self.ReOrder_FUNC(biggest)[1][0])
                        self.C3=list(self.ReOrder_FUNC(biggest)[2][0])
                        self.C4=list(self.ReOrder_FUNC(biggest)[3][0])
                    else:
                        self.C1=[0,0]
                        self.C2=[int(W),0]
                        self.C3=[int(W),int(H)]
                        self.C4=[0,int(H)]
                            
                    self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)
                    self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],self.Circle_Radius,self.MainCanvas1,"red")
                    self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],self.Circle_Radius,self.MainCanvas1,"red")
                    self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],self.Circle_Radius,self.MainCanvas1,"red")
                    self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],self.Circle_Radius,self.MainCanvas1,"red")
                    self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
                    self.Xbar.config(command=self.MainCanvas1.xview)
                    self.Ybar.config(command=self.MainCanvas1.yview)
                    self.MainCanvas1.yview_moveto(0.0)
                    self.MainCanvas1.xview_moveto(0.0)
                else:
                    self.fixed_ratio=x
                    msgbox.showwarning("Warning","The Image would be too small")
            else:
                msgbox.showwarning("warning",f"The {data} \nhas been deleted/Moved")
        else:
            msgbox.showerror("Error","There is no Image")
        pass

    #----------Creating the Circle----------
    def create_circle(self,x, y, r, canvasName,color="red"):
        x0 = x - r
        y0 = y - r
        x1 = x + r
        y1 = y + r
        return canvasName.create_oval(x0, y0, x1, y1,fill=color,outline="black",width=1,activefill="yellow")
    
    #----------Change the Points with mouse move----------
    def Change_Points(self,e):
        x_axis=int(self.MainCanvas1.canvasx(e.x))
        y_axis=int(self.MainCanvas1.canvasy(e.y))
        self.element=self.MainCanvas1.find_withtag(CURRENT)
        if self.element==():
            pass
        else:
            self.MainCanvas1.config(cursor="hand2")
            if self.element[0]==self.MainCanvas1.find_withtag(self.C1_cirlce)[0]:
                self.MainCanvas1.moveto(self.C1_cirlce,x_axis-8,y_axis-8)
                self.MainCanvas1.coords(self.Point_Line,x_axis,y_axis,self.C2[0],self.C2[1],self.C3[0],self.C3[1],self.C4[0],self.C4[1])
                self.C1=[x_axis,y_axis]
                self.Circle_Label.config(text=f"C1 = {self.C1}")
                self.Magnifying_FUNC(self.C1[0],self.C1[1])
                self.MainCanvas1.config(scrollregion=self.MainCanvas1.bbox(ALL),xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set)
                self.Xbar.config(command=self.MainCanvas1.xview)
                self.Ybar.config(command=self.MainCanvas1.yview)

            if self.element[0]==self.MainCanvas1.find_withtag(self.C2_cirlce)[0]:
                self.MainCanvas1.moveto(self.C2_cirlce,x_axis-8,y_axis-8)
                self.MainCanvas1.coords(self.Point_Line,self.C1[0],self.C1[1],x_axis,y_axis,self.C3[0],self.C3[1],self.C4[0],self.C4[1])
                self.C2=[x_axis,y_axis]
                self.Circle_Label.config(text=f"C2 = {self.C2}")
                self.Magnifying_FUNC(self.C2[0],self.C2[1])
                self.MainCanvas1.config(scrollregion=self.MainCanvas1.bbox(ALL),xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set)
                self.Xbar.config(command=self.MainCanvas1.xview)
                self.Ybar.config(command=self.MainCanvas1.yview)

            if self.element[0]==self.MainCanvas1.find_withtag(self.C3_cirlce)[0]:
                self.MainCanvas1.moveto(self.C3_cirlce,x_axis-8,y_axis-8)
                self.MainCanvas1.coords(self.Point_Line,self.C1[0],self.C1[1],self.C2[0],self.C2[1],x_axis,y_axis,self.C4[0],self.C4[1])
                self.C3=[x_axis,y_axis]
                self.Circle_Label.config(text=f"C3 = {self.C3}")
                self.Magnifying_FUNC(self.C3[0],self.C3[1])
                self.MainCanvas1.config(scrollregion=self.MainCanvas1.bbox(ALL),xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set)
                self.Xbar.config(command=self.MainCanvas1.xview)
                self.Ybar.config(command=self.MainCanvas1.yview)

            if self.element[0]==self.MainCanvas1.find_withtag(self.C4_cirlce)[0]:
                self.MainCanvas1.moveto(self.C4_cirlce,x_axis-8,y_axis-8)
                self.MainCanvas1.coords(self.Point_Line,self.C1[0],self.C1[1],self.C2[0],self.C2[1],self.C3[0],self.C3[1],x_axis,y_axis)
                self.C4=[x_axis,y_axis]
                self.Circle_Label.config(text=f"C4 = {self.C4}")
                self.Magnifying_FUNC(self.C4[0],self.C4[1])
                self.MainCanvas1.config(scrollregion=self.MainCanvas1.bbox(ALL),xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set)
                self.Xbar.config(command=self.MainCanvas1.xview)
                self.Ybar.config(command=self.MainCanvas1.yview)
        pass

    #----------Change the Mouse cursor normal----------
    def Change_mouse_Normal(self,*args):
        self.MainCanvas1.config(cursor="arrow")
        pass

    #----------Auto Scan Function----------
    def Auto_Scan_FUNC(self,img,thrs=[0,100],minarea=10000):
        img=cv2.cvtColor(img,cv2.COLOR_BGR2GRAY)
        img=cv2.GaussianBlur(img,(11,11),0)
        # imgcanny=cv2.Canny(img,thrs[0],thrs[1])
        thresh_img=cv2.adaptiveThreshold(img,255,cv2.ADAPTIVE_THRESH_MEAN_C,cv2.THRESH_BINARY,21,5)
        thresh_img=255-thresh_img
        kernel=np.ones((5,5))
        imgdial=cv2.dilate(thresh_img,kernel=kernel,iterations=3)
        imgerode=cv2.erode(imgdial,kernel,iterations=1)
        # show_img=cv2.resize(imgerode,(0,0),fx=0.3,fy=0.3)
        # cv2.imshow("Image",show_img)

        contour,hieracy=cv2.findContours(imgerode,cv2.RETR_LIST,cv2.CHAIN_APPROX_SIMPLE)
        contour=sorted(contour,key=cv2.contourArea,reverse=True)
        finalContours=[]
        for i in contour:
            area=cv2.contourArea(i)
            if area>minarea:
                peri=cv2.arcLength(i,True)
                approx=cv2.approxPolyDP(i,peri*0.11,True)
                if len(approx)==4:
                    finalContours.append([approx,area])
        finalContours=sorted(finalContours,key=lambda x: x[1],reverse=True)
        if finalContours:
            return finalContours
        else:
            return None

    #----------Reorder Function----------
    def ReOrder_FUNC(self,mypoints):
        mynewpoint=np.zeros_like(mypoints)
        mypoint=mypoints.reshape((4,2))
        add=mypoint.sum(1)
        mynewpoint[0]=mypoint[np.argmin(add)]
        mynewpoint[2]=mypoint[np.argmax(add)]
        diff=np.diff(mypoint,axis=1)
        mynewpoint[1]=mypoint[np.argmin(diff)]
        mynewpoint[3]=mypoint[np.argmax(diff)]
        return mynewpoint

    #----------Magnifying Glass Function----------
    def Magnifying_FUNC(self,pointX,pointY):
        self.Crop_img=self.image.copy().crop((pointX-30,pointY-30,pointX+30,pointY+30))
        W,H=self.Crop_img.size
        self.Crop_img=self.Crop_img.resize((int(W*2),int(H*2)),Image.ANTIALIAS)
        self.Crop_img=ImageEnhance.Contrast(self.Crop_img).enhance(2)
        draw = ImageDraw.Draw(self.Crop_img)
        r=3
        leftUpPoint = (W-r, H-r)
        rightDownPoint = (W+r, H+r)
        twoPointList = [leftUpPoint, rightDownPoint]
        draw.line((0,int(H),W*2,H),fill="#9400D3",width=3)
        draw.line((W,0,W,W*2),fill="#9400D3",width=3)
        draw.ellipse(twoPointList, fill="red",outline="black")
        self.Crop_img.thumbnail((150,150))
        self.Crop_imgtk=ImageTk.PhotoImage(self.Crop_img)
        self.Magnifying_Glass_Label.config(image=self.Crop_imgtk)
        self.Magnifying_Glass_Label.image=self.Crop_imgtk
        pass

    #----------Rotating the Scan Image----------
    def Rotation_image_Left(self,*args):
        self.root.focus()
        if self.SCAN_Active==True and self.C1_cirlce in self.MainCanvas1.find_all():
            n=len(self.ROTATION_List)-1
            self.Rotate_Point=self.Rotate_Point+1
            if self.Rotate_Point<n:
                data=self.ListBox_Combo.get()
                if os.path.isfile(data):
                    imgc=Image.open(data)
                    imgc=imgc.rotate(self.ROTATION_List[self.Rotate_Point],Image.ANTIALIAS,expand=1)
                    self.MainCanvas1.delete(ALL)
                    # import image in canvas
                    self.opencvImage=cv2.resize(np.array(imgc),(0, 0), fx = self.fixed_ratio, fy = self.fixed_ratio,interpolation=cv2.INTER_LANCZOS4)
                    self.image=Image.fromarray(self.opencvImage)
                            
                    W,H=self.opencvImage.shape[1],self.opencvImage.shape[0]
                    self.Image_Height=H
                    self.Image_Width=W
                        
                    imgtk=ImageTk.PhotoImage(image=self.image)
                    self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
                    self.MainCanvas1.image=imgtk
                    # polygon
                    # auto scan
                    conts=self.Auto_Scan_FUNC(self.opencvImage)
                    if conts and self.Auto_Scan_Active==True:
                        biggest=conts[0][0]
                        self.C1=list(self.ReOrder_FUNC(biggest)[0][0])
                        self.C2=list(self.ReOrder_FUNC(biggest)[1][0])
                        self.C3=list(self.ReOrder_FUNC(biggest)[2][0])
                        self.C4=list(self.ReOrder_FUNC(biggest)[3][0])
                    else:
                        self.C1=[0,0]
                        self.C2=[int(W),0]
                        self.C3=[int(W),int(H)]
                        self.C4=[0,int(H)]
                            
                    self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)

                    self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],self.Circle_Radius,self.MainCanvas1,"red")
                    self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],self.Circle_Radius,self.MainCanvas1,"red")
                    self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],self.Circle_Radius,self.MainCanvas1,"red")
                    self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],self.Circle_Radius,self.MainCanvas1,"red")
                    
                    self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
                    self.Xbar.config(command=self.MainCanvas1.xview)
                    self.Ybar.config(command=self.MainCanvas1.yview)
                    self.MainCanvas1.yview_moveto(0.0)
                    self.MainCanvas1.xview_moveto(0.0)
                else:
                    msgbox.showwarning("warning",f"The {data} \nhas been deleted/Moved")
                pass
            else:
                self.Rotate_Point=0
                data=self.ListBox_Combo.get()
                if os.path.isfile(data):
                    imgc=Image.open(data)
                    imgc=imgc.rotate(self.ROTATION_List[self.Rotate_Point],Image.ANTIALIAS,expand=1)
                    self.MainCanvas1.delete(ALL)
                    # import image in canvas
                    self.opencvImage=cv2.resize(np.array(imgc),(0, 0), fx = self.fixed_ratio, fy = self.fixed_ratio,interpolation=cv2.INTER_LANCZOS4)
                    self.image=Image.fromarray(self.opencvImage)
                            
                    W,H=self.opencvImage.shape[1],self.opencvImage.shape[0]
                    self.Image_Height=H
                    self.Image_Width=W
                        
                    imgtk=ImageTk.PhotoImage(image=self.image)
                    self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
                    self.MainCanvas1.image=imgtk
                    # polygon
                    # auto scan
                    conts=self.Auto_Scan_FUNC(self.opencvImage)
                    if conts and self.Auto_Scan_Active==True:
                        biggest=conts[0][0]
                        self.C1=list(self.ReOrder_FUNC(biggest)[0][0])
                        self.C2=list(self.ReOrder_FUNC(biggest)[1][0])
                        self.C3=list(self.ReOrder_FUNC(biggest)[2][0])
                        self.C4=list(self.ReOrder_FUNC(biggest)[3][0])
                    else:
                        self.C1=[0,0]
                        self.C2=[int(W),0]
                        self.C3=[int(W),int(H)]
                        self.C4=[0,int(H)]
                            
                    self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)

                    self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],5,self.MainCanvas1,"red")
                    self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],5,self.MainCanvas1,"red")
                    self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],5,self.MainCanvas1,"red")
                    self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],5,self.MainCanvas1,"red")
                    
                    self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
                    self.Xbar.config(command=self.MainCanvas1.xview)
                    self.Ybar.config(command=self.MainCanvas1.yview)
                    self.MainCanvas1.yview_moveto(0.0)
                    self.MainCanvas1.xview_moveto(0.0)
                else:
                    msgbox.showwarning("warning",f"The {data} \nhas been deleted/Moved")
        else:
            msgbox.showerror("Error","There is no Image")
        pass

    #||||||||||||||||||||||||||||| Setting Window |||||||||||||||||||||||||||||

    #----------Setting Window----------
    def Setting_WIN_FUNC(self,*args):
        if self.Setting_Active==False:
            self.Setting_Win=Toplevel()
            self.Setting_Win.title("Setting")
            self.Setting_Win.resizable(0,0)
            self.Setting_Win.geometry("+0+0")
            self.Setting_Win.wm_protocol("WM_DELETE_WINDOW",self.Close_Setting_WIN_FUNC)
            try:
                self.Setting_Win.wm_iconbitmap(self.APP_LOGO)
            except:
                pass
            # notebook
            self.Setting_NoteBook=ttk.Notebook(self.Setting_Win)
            self.Setting_NoteBook.pack(fill=BOTH,expand=True)
            # Label Frame
            L1=LabelFrame(self.Setting_NoteBook,font=("arial",20,"bold"),bg="#00002c",fg="black",border=1,relief=SOLID,highlightthickness=1,highlightcolor="yellow",highlightbackground="yellow")
            # labels
            Label(L1,text="Image Filters",font=("arial",15,"bold"),bg="#6c09ed",fg="yellow",border=1,relief=SOLID).grid(row=0,column=0,columnspan=4,padx=2,pady=2,sticky="nswe")

            # radio button
            self.RadioValue=IntVar()
            self.R1=ttk.Radiobutton(L1,text="Original",value=0,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R1.grid(row=1,column=0,pady=2,padx=2,sticky="nswe")
            self.R2=ttk.Radiobutton(L1,text="Gray Scale",value=1,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R2.grid(row=1,column=1,pady=2,padx=2,sticky="nswe")
            self.R3=ttk.Radiobutton(L1,text="Bright",value=2,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R3.grid(row=1,column=2,pady=2,padx=2,sticky="nswe")
            self.R4=ttk.Radiobutton(L1,text="sharpening",value=3,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R4.grid(row=1,column=3,pady=2,padx=2,sticky="nswe")
            self.R5=ttk.Radiobutton(L1,text="Red",value=4,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R5.grid(row=2,column=0,pady=2,padx=2,sticky="nswe")
            self.R6=ttk.Radiobutton(L1,text="Blue",value=5,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R6.grid(row=2,column=1,pady=2,padx=2,sticky="nswe")
            self.R7=ttk.Radiobutton(L1,text="Green",value=6,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R7.grid(row=2,column=2,pady=2,padx=2,sticky="nswe")
            self.R8=ttk.Radiobutton(L1,text="Yellow",value=7,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R8.grid(row=2,column=3,pady=2,padx=2,sticky="nswe")
            self.R9=ttk.Radiobutton(L1,text="Gamma",value=8,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R9.grid(row=3,column=0,pady=2,padx=2,sticky="nswe")
            self.R10=ttk.Radiobutton(L1,text="Contrast",value=9,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R10.grid(row=3,column=1,pady=2,padx=2,sticky="nswe")
            self.R11=ttk.Radiobutton(L1,text="Binary",value=10,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R11.grid(row=3,column=2,pady=2,padx=2,sticky="nswe")
            self.R12=ttk.Radiobutton(L1,text="Binary INV",value=11,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R12.grid(row=3,column=3,pady=2,padx=2,sticky="nswe")
            self.R13=ttk.Radiobutton(L1,text="Blur",value=12,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R13.grid(row=4,column=0,pady=2,padx=2,sticky="nswe")
            self.R14=ttk.Radiobutton(L1,text="Sketch",value=13,variable=self.RadioValue,cursor="hand2",command=self.Change_RadioButton_FUNC)
            self.R14.grid(row=4,column=1,pady=2,padx=2,sticky="nswe")

            self.RadioValue.set(self.Image_Effect_Number)

            ttk.Separator(L1,orient=HORIZONTAL).grid(row=5,column=0,columnspan=4,padx=2,pady=2,sticky="ew")

            # Fixed Size
            self.CH_Value=IntVar()
            self.CH=ttk.Checkbutton(L1,text="Fixed Size",cursor="hand2",offvalue=0,onvalue=1,variable=self.CH_Value,command=self.Checkbox_Click_FUNC)
            self.CH.grid(row=6,column=0,columnspan=4,padx=2,pady=10,sticky="nswe")
            # self.CH_Value.set(0)

            self.Height_Value=IntVar()
            self.Width_Value=IntVar()

            Label(L1,text="Height",font=("arial",12,"bold"),bg="#00002c",fg="white").grid(row=7,column=0,pady=2,padx=2,sticky="nswe")
            Label(L1,text="Width",font=("arial",12,"bold"),bg="#00002c",fg="white").grid(row=8,column=0,pady=2,padx=2,sticky="nswe")
            self.E1=ttk.Entry(L1,font=("Calibri",14),state=DISABLED,textvariable=self.Height_Value,justify=CENTER)
            self.E1.grid(row=7,column=1,columnspan=3,padx=2,pady=2,sticky="nswe")
            self.E2=ttk.Entry(L1,font=("Calibri",14),state=DISABLED,textvariable=self.Width_Value,justify=CENTER)
            self.E2.grid(row=8,column=1,columnspan=3,padx=2,pady=2,sticky="nswe")
            self.Height_Value.set(self.PDF_Height)
            self.Width_Value.set(self.PDF_Width)

            if self.Fixed_PDF_PAGE==True:
                self.E1.configure(state=NORMAL)
                self.E2.configure(state=NORMAL)
                self.CH_Value.set(1)
            elif self.Fixed_PDF_PAGE==False:
                self.E1.configure(state=DISABLED)
                self.E2.configure(state=DISABLED)
                self.CH_Value.set(0)

            ttk.Separator(L1,orient=HORIZONTAL).grid(row=9,column=0,columnspan=4,padx=2,pady=2,sticky="ew")
            # change database file
            Label(L1,text="Database File",font=("arial",12,"bold"),bg="#6c09ed",fg="black").grid(row=10,column=0,padx=2,pady=9,sticky="nswe")
            self.L2=Label(L1,text=f"{self.DataBase_FILE}",font=("arial",12,"bold"),bg="#00002c",fg="white")
            self.L2.grid(row=10,column=1,columnspan=2,pady=9,padx=2,sticky="nswe")

            Button(L1,text="Create/Change DB",font=("arial",12,"bold"),bg="yellow",fg="black",border=0,activebackground="#6c09ed",activeforeground="yellow",cursor="hand2",command=self.Change_Database_File_FUNC).grid(row=10,column=3,padx=2,pady=9,sticky="nswe")
            # OCR font size
            Label(L1,text="OCR Font Size",font=("arial",12,"bold"),bg="#6c09ed",fg="black").grid(row=11,column=0,pady=10,padx=2,sticky="nswe")
            
            self.Font_Size_Value=IntVar()
            self.Font_Size_Slider=ttk.Scale(L1,from_=0,to=50,variable=self.Font_Size_Value,command=self.Font_Size_OCR_FUNC)
            self.Font_Size_Slider.grid(row=11,column=1,columnspan=2,pady=10,padx=2,sticky="nswe")

            self.Font_Size_label=Label(L1,text="12",font=("arial",12,"bold"),bg="#6c09ed",fg="black")
            self.Font_Size_label.grid(row=11,column=3,pady=10,padx=2,sticky="nswe")
            # change the backup_folder name
            Label(L1,text="Database File",font=("arial",12,"bold"),bg="#6c09ed",fg="black").grid(row=12,column=0,padx=2,pady=9,sticky="nswe")
            self.L3=Label(L1,text=f"{self.Backup_Folder}",font=("arial",12,"bold"),bg="#00002c",fg="white")
            self.L3.grid(row=12,column=1,columnspan=2,pady=9,padx=2,sticky="nswe")

            Button(L1,text="Change BackUP",font=("arial",12,"bold"),bg="yellow",fg="black",border=0,activebackground="#6c09ed",activeforeground="yellow",cursor="hand2",command=self.Change_BackUP_Name_FUNC).grid(row=12,column=3,padx=2,pady=9,sticky="nswe")


            # ok button
            Button(L1,text="Preview",font=("arial",12,"bold"),bg="#ee015c",fg="yellow",activebackground="#00002c",activeforeground="yellow",cursor="hand2",border=0,command=self.Preview_Scanning_FUNC).grid(row=13,column=0,padx=2,pady=2,sticky="nswe")
            Button(L1,text="OK",font=("arial",12,"bold"),bg="#ee015c",fg="yellow",activebackground="#00002c",activeforeground="yellow",cursor="hand2",border=0,command=self.Setting_Save_FUNC).grid(row=13,column=1,columnspan=3,padx=2,pady=2,sticky="nswe")
            L1.focus()

            L1.pack(fill=BOTH,expand=True)

            # Filter Setting
            L2=Frame(self.Setting_NoteBook,bg="#00002c",border=1,relief=SOLID,highlightthickness=1,highlightbackground="yellow",highlightcolor="yellow")
            L2.columnconfigure(1,weight=1)
            for i in range(8):
                L2.rowconfigure(i,weight=1)

            # labels
            Label(L2,text="Gamma",bg="#6c09ed",fg="white",font=("arial",12,"bold"),borderwidth=1,relief=SOLID).grid(row=0,column=0,padx=2,pady=2,sticky="nswe")
            Label(L2,text="Sharpen",bg="#6c09ed",fg="white",font=("arial",12,"bold"),borderwidth=1,relief=SOLID).grid(row=1,column=0,padx=2,pady=2,sticky="nswe")
            Label(L2,text="Contrast",bg="#6c09ed",fg="white",font=("arial",12,"bold"),borderwidth=1,relief=SOLID).grid(row=2,column=0,padx=2,pady=2,sticky="nswe")
            Label(L2,text="Threshold",bg="#6c09ed",fg="white",font=("arial",12,"bold"),borderwidth=1,relief=SOLID).grid(row=3,column=0,padx=2,pady=2,sticky="nswe")
            Label(L2,text="Blur",bg="#6c09ed",fg="white",font=("arial",12,"bold"),borderwidth=1,relief=SOLID).grid(row=4,column=0,padx=2,pady=2,sticky="nswe")
            Label(L2,text="Bright",bg="#6c09ed",fg="white",font=("arial",12,"bold"),borderwidth=1,relief=SOLID).grid(row=5,column=0,padx=2,pady=2,sticky="nswe")

            # scales
            # gamma=0.5,sharpen=4,contracts=2,thresh_C=17,blur_n=3
            self.gamma_Value=DoubleVar()
            self.sharphen_Value=IntVar()
            self.Contrast_Value=IntVar()
            self.Thresh_Value=IntVar()
            self.Blur_Value=IntVar()
            self.Bright_Value=IntVar()

            Scale(L2,from_=0.1,to=1.0,resolution=0.1,activebackground="yellow",variable=self.gamma_Value,orient=HORIZONTAL,font=("arial",12,"bold"),command=self.Advanced_Setting_FUNC,troughcolor="white",cursor="hand2",borderwidth=0,highlightthickness=0,bg="#00002c",fg="yellow").grid(row=0,column=1,columnspan=3,padx=2,pady=10,sticky="nswe")
            Scale(L2,from_=0,to=20,variable=self.sharphen_Value,activebackground="yellow",orient=HORIZONTAL,font=("arial",12,"bold"),command=self.Advanced_Setting_FUNC,troughcolor="white",cursor="hand2",borderwidth=0,highlightthickness=0,bg="#00002c",fg="yellow").grid(row=1,column=1,columnspan=3,padx=2,pady=10,sticky="nswe")
            Scale(L2,from_=0,to=10,variable=self.Contrast_Value,activebackground="yellow",orient=HORIZONTAL,font=("arial",12,"bold"),command=self.Advanced_Setting_FUNC,troughcolor="white",cursor="hand2",borderwidth=0,highlightthickness=0,bg="#00002c",fg="yellow").grid(row=2,column=1,columnspan=3,padx=2,pady=10,sticky="nswe")
            Scale(L2,from_=0,to=20,variable=self.Thresh_Value,activebackground="yellow",orient=HORIZONTAL,font=("arial",12,"bold"),command=self.Advanced_Setting_FUNC,troughcolor="white",cursor="hand2",borderwidth=0,highlightthickness=0,bg="#00002c",fg="yellow").grid(row=3,column=1,columnspan=3,padx=2,pady=10,sticky="nswe")
            Scale(L2,from_=0,to=100,variable=self.Bright_Value,activebackground="yellow",orient=HORIZONTAL,font=("arial",12,"bold"),command=self.Advanced_Setting_FUNC,troughcolor="white",cursor="hand2",borderwidth=0,highlightthickness=0,bg="#00002c",fg="yellow").grid(row=5,column=1,columnspan=3,padx=2,pady=10,sticky="nswe")
            # blur radio buttons
            F1=Frame(L2)
            F1.columnconfigure(0,weight=1)
            F1.columnconfigure(1,weight=1)
            F1.columnconfigure(2,weight=1)
            F1.rowconfigure(0,weight=1)
            ttk.Radiobutton(F1,value=1,text="1",variable=self.Blur_Value,command=self.Advanced_Setting_FUNC,cursor="hand2").grid(row=0,column=0,sticky="nswe")
            ttk.Radiobutton(F1,value=3,text="3",variable=self.Blur_Value,command=self.Advanced_Setting_FUNC,cursor="hand2").grid(row=0,column=1,sticky="nswe")
            ttk.Radiobutton(F1,value=9,text="9",variable=self.Blur_Value,command=self.Advanced_Setting_FUNC,cursor="hand2").grid(row=0,column=2,sticky="nswe")
            F1.grid(row=4,column=1,padx=2,pady=10,sticky="nswe")

            self.gamma_Value.set(self.Gamma_NO)
            self.sharphen_Value.set(self.Sharpen_NO)
            self.Contrast_Value.set(self.Contrast_NO)
            self.Thresh_Value.set(self.Thresh_NO)
            self.Blur_Value.set(self.Blut_NO)
            self.Bright_Value.set(self.Bright_NO)
            # preview button
            self.Settings_Preview_Button=Button(L2,text="Preview Scan",font=("arial",20,"bold"),bg="#fe1f54",fg="yellow",borderwidth=2,relief=SOLID,cursor="hand2",command=self.Advanced_Setting_Preview_FUNC)
            self.Settings_Preview_Button.grid(row=6,column=0,columnspan=2,padx=2,pady=2,sticky="nswe")

            L2.focus()
            L2.pack(fill=BOTH,expand=True)

            # Advanced Settings
            L3=Frame(self.Setting_NoteBook,bg="#00002c",border=1,relief=SOLID,highlightthickness=1,highlightbackground="yellow",highlightcolor="yellow")
            L3.columnconfigure(0,weight=1)
            L3.columnconfigure(1,weight=1)

            self.Save_Records_value=IntVar()
            self.Auto_value=IntVar()
            self.Save_Records_Button=ttk.Checkbutton(L3,text="Save Record and Backup",variable=self.Save_Records_value,command=self.Save_Records_FUNC,cursor="hand2")
            self.Save_Records_Button.grid(row=0,column=0,padx=2,pady=2,sticky="nswe")

            self.AutoScan_Button=ttk.Checkbutton(L3,text="Automatic Scan",variable=self.Auto_value,command=self.Auto_Scan_Active_FUNC,cursor="hand2")
            self.AutoScan_Button.grid(row=1,column=0,padx=2,pady=2,sticky="nswe")
            self.constant_size_Value=IntVar()
            self.Constant_size_Button=ttk.Checkbutton(L3,text="Constant Size Ratio",variable=self.constant_size_Value,cursor="hand2",command=self.Constant_Size_Active_FUNC,onvalue=1,offvalue=0)
            self.Constant_size_Button.grid(row=2,column=0,padx=2,pady=2,sticky="nswe")
            # Image Height and width
            self.Image_Height_Label=Label(L3,text="Height = None",font=("arial",12,"bold"),anchor="nw",bg="#0f0026",fg="yellow",padx=2,pady=2)
            self.Image_Height_Label.grid(row=5,column=0,padx=2,pady=2,sticky="nswe")

            self.Image_Width_Label=Label(L3,text="Width = None",font=("arial",12,"bold"),anchor="nw",bg="#0f0026",fg="yellow",padx=2,pady=2)
            self.Image_Width_Label.grid(row=6,column=0,padx=2,pady=2,sticky="nswe")

            self.Image_Height_Label.config(text=f"Height = {self.Image_Height} pixels")
            self.Image_Width_Label.config(text=f"Width = {self.Image_Width} pixels")

            ttk.Separator(L3,orient=HORIZONTAL).grid(row=7,column=0,columnspan=2,padx=2,pady=2,sticky="ew")

            # Tesseract OCR Location
            Label(L3,text="Tesseract Path",font=("arial",12,"bold","underline"),bg="#00002c",fg="yellow",border=0).grid(row=8,column=0,columnspan=2,padx=2,pady=2,sticky="nswe")
            self.Tesseract_Label = Label(L3,text=f"{self.TESSERACT_PATH}",font=("arial",12,"bold"),anchor="nw",bg="#0f0026",fg="yellow",padx=2,pady=2)
            self.Tesseract_Label.grid(row=9,column=0,columnspan=2,padx=2,pady=6,sticky="nswe")

            ttk.Separator(L3,orient=HORIZONTAL).grid(row=10,column=0,columnspan=2,padx=2,pady=2,sticky="ew")
            # reset Add list button
            Button(L3,text="Reset ADD List",font=("arial",15,"bold"),bg="#fe1f54",fg="yellow",cursor="hand2",border=0,command=self.Reset_ADDED_LIST_FUNC).grid(row=11,column=0,columnspan=2,padx=2,pady=10,sticky="nswe")
            # show side tools
            Button(L3,text="Side Window ☰",font=("arial",15,"bold"),bg="#fe1f54",fg="yellow",cursor="hand2",border=0,command=self.Show_Hide_Tools_FUNC).grid(row=12,column=0,columnspan=2,padx=2,pady=10,sticky="nswe")
            # full screen button
            if self.FullScreen_Active==True:
                txt="Normal Screen"
            if self.FullScreen_Active==False:
                txt="Full Screen \u26F6"
            self.FullScreen_Button=Button(L3,text=txt,font=("arial",15,"bold"),bg="#fe1f54",fg="yellow",cursor="hand2",border=0,command=self.FullScreen_FUNC)
            self.FullScreen_Button.grid(row=13,column=0,columnspan=2,padx=2,pady=10,sticky="nswe")

            if self.Save_Records==True:
                self.Save_Records_value.set(1)
            elif self.Save_Records==False:
                self.Save_Records_value.set(0)

            if self.Auto_Scan_Active==True:
                self.Auto_value.set(1)
            elif self.Auto_Scan_Active==False:
                self.Auto_value.set(0)

            if self.Constant_size_Active==True:
                self.constant_size_Value.set(1)
            elif self.Constant_size_Active==False:
                self.constant_size_Value.set(0)

            L3.pack(fill=BOTH,expand=True)

            self.Setting_NoteBook.add(L1,text="Setting",padding=(-1, -1, -3, -3))
            self.Setting_NoteBook.add(L2,text="Filter Setting",padding=(-1, -1, -3, -3))
            self.Setting_NoteBook.add(L3,text="Advanced Setting",padding=(-1, -1, -3, -3))
            self.Setting_Win.bind("<Return>",self.Setting_Save_FUNC)

            self.Setting_NoteBook.bind("<<NotebookTabChanged>>",lambda e:self.Setting_Win.focus())
            self.Setting_Win.grab_set()

            self.Setting_Active=True
            self.Setting_Win.focus()
        elif self.Setting_Active==True:
            self.Setting_Win.focus()
        pass

    #----------Closing Setting window Function----------
    def Close_Setting_WIN_FUNC(self,*args):
        self.Setting_Win.destroy()
        self.Setting_Active=False
        pass

    #----------Save Record Function----------
    def Save_Records_FUNC(self,*args):
        if self.Save_Records==True:
            self.Save_Records_value.set(0)
            self.Save_Records=False
        elif self.Save_Records==False:
            self.Save_Records_value.set(1)
            self.Save_Records=True
        self.Setting_Win.focus()
        pass

    #----------Auto Scan Function----------
    def Auto_Scan_Active_FUNC(self,*args):
        if self.Auto_Scan_Active==True:
            self.Auto_value.set(0)
            self.Auto_Scan_Active=False
        elif self.Auto_Scan_Active==False:
            self.Auto_value.set(1)
            self.Auto_Scan_Active=True
        self.Setting_Win.focus()
        pass

    #----------Auto Scan Function----------
    def Constant_Size_Active_FUNC(self,*args):
        if self.Constant_size_Active==True:
            self.constant_size_Value.set(0)
            self.Constant_size_Active=False
            self.Constant_Size=0.5
        elif self.Constant_size_Active==False:
            self.constant_size_Value.set(1)
            self.Constant_size_Active=True
        self.Setting_Win.focus()
        pass

    #----------Change Filter Function----------
    def Change_RadioButton_FUNC(self,*args):
        x=self.RadioValue.get()
        self.Image_Effect_Number=x
        self.Setting_Win.focus()
        pass

    #----------Advanced Setting Function----------
    def Advanced_Setting_FUNC(self,*args):
        self.Gamma_NO=self.gamma_Value.get()
        self.Sharpen_NO=self.sharphen_Value.get()
        self.Contrast_NO=self.Contrast_Value.get()
        self.Thresh_NO=self.Thresh_Value.get()
        self.Blut_NO=self.Blur_Value.get()
        self.Bright_NO=self.Bright_Value.get()
        pass

    #----------Advanced Setting Preview Function----------
    def Advanced_Setting_Preview_FUNC(self,*args):
        if len(self.Org_List)!=0:
            self.Preview_Scanning_FUNC()
            self.Setting_Win.focus()
        else:
            msgbox.showerror("Error","There is no Image")
        pass

    #----------Font Size Function----------
    def Font_Size_OCR_FUNC(self,*args):
        if self.OCR_Active==True:
            no=self.Font_Size_Value.get()
            self.Font_Size_Value.set(no)
            self.Font_Size_label.config(text=f"{12+no}")
            self.OCR_TextBox.config(font=("arial",12+no))
        else:
            self.Font_Size_Value.set(0)
        pass

    #----------Reset Add List Function----------
    def Reset_ADDED_LIST_FUNC(self,*args):
        if len(self.PDF_ADD_LIST):
            asks=msgbox.askquestion("Reset","Do you want to reset the ADD List")
            if asks=="yes":
                self.PDF_ADD_LIST=[]
                self.List_ADDED_Label.config(text="")
                msgbox.showinfo("Success","The ADD List has been Reset")
            else:
                msgbox.showinfo("Reset","The ADD lIst hasn't been Reset")
        else:
            msgbox.showwarning("Warning","There are no Image/Images Added in the 'ADD List'")
        pass

    #----------Changed Database file location----------
    def Change_Database_File_FUNC(self,*args):
        files=filedialog.asksaveasfilename(defaultextension=".db",title="Create/Change")
        if files!="":
            self.DataBase_FILE=files
            self.backup_path_part1=os.path.dirname(self.DataBase_FILE).replace('\\','/')
            self.Backup_Path=f"{self.backup_path_part1}/{self.Backup_Folder}"
            self.L2.configure(text=self.DataBase_FILE)
        pass

    #----------Changed BackUP Folder Name----------
    def Change_BackUP_Name_FUNC(self,*args):
        names=simpledialog.askstring("Backup","Enter the Backup Folder Name")
        if names!="":
            self.Backup_Folder=names
            self.backup_path_part1=os.path.dirname(self.DataBase_FILE).replace('\\','/')
            self.Backup_Path=f"{self.backup_path_part1}/{self.Backup_Folder}"
            self.L3.config(text=self.Backup_Folder)
        pass

    #----------Checkbox clicked function----------
    def Checkbox_Click_FUNC(self,*args):
        if self.CH_Value.get()==0:
            self.E1.config(state=DISABLED)
            self.E2.config(state=DISABLED)
            pass
        if self.CH_Value.get()==1:
            self.E1.config(state=NORMAL)
            self.E2.config(state=NORMAL)
            pass
        pass

    #----------Save The Change in settings function----------
    def Setting_Save_FUNC(self,*args):
        try:
            x=self.RadioValue.get()
            self.Image_Effect_Number=x

            y=self.CH_Value.get()
            if y==0:
                self.Fixed_PDF_PAGE=False
                self.Setting_Win.destroy()
                msgbox.showinfo("Done","The Changes has been Done!")
            elif y==1:
                self.Fixed_PDF_PAGE=True
                if self.Height_Value.get()>100 and self.Width_Value.get()>100:
                    self.PDF_Height=self.Height_Value.get()
                    self.PDF_Width=self.Width_Value.get()
                    self.Setting_Win.destroy() 
                    msgbox.showinfo("Done","The Changes has been Done!")
                else:
                    msgbox.showwarning("Warning","The Image cannot be less than 100x100 pixels")
                    self.Height_Value.set(self.PDF_Height)
                    self.Width_Value.set(self.PDF_Width)
            self.Setting_Active=False
        except Exception as e:
            msgbox.showerror("Error",f"{e}")
        pass

    #||||||||||||||||||||||||||||| To Scaning and Export |||||||||||||||||||||||||||||

    #----------Adding the Scan image into the List----------
    def Adding_Scan_Image_FUNC(self,*args):
        if self.C1_cirlce in self.MainCanvas1.find_all():
            self.Points=self.MainCanvas1.coords(self.Point_Line)
            width=abs(self.Points[0]-self.Points[2])
            height=abs(self.Points[1]-self.Points[7])
            if self.Fixed_PDF_PAGE==False:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,width,height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            elif self.Fixed_PDF_PAGE==True:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,self.PDF_Width,self.PDF_Height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            self.image=Image.fromarray(scanimg).convert("RGB")
            try:
                dpi_x, dpi_y = self.image.info["dpi"]
            except KeyError:
                dpi_x, dpi_y = (self.wanted_dpi,self.wanted_dpi)
            self.image = self.image.resize((round(self.image.width*self.wanted_dpi/dpi_x), round(self.image.height*self.wanted_dpi/dpi_y)), resample=Image.LANCZOS)
            self.opencvImage=np.array(self.image)
            W,H=self.image.size
            self.MainCanvas1.delete(ALL)

            imgtk=ImageTk.PhotoImage(self.image)
            self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
            self.MainCanvas1.image=imgtk
            self.MainCanvas1.yview_moveto(0.0)

            # polygon
            self.C1=[0,0]
            self.C2=[int(W),0]
            self.C3=[int(W),int(H)]
            self.C4=[0,int(H)]
                    
            self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)

            self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],self.Circle_Radius,self.MainCanvas1,"red")
            self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],self.Circle_Radius,self.MainCanvas1,"red")
            self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],self.Circle_Radius,self.MainCanvas1,"red")
            self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],self.Circle_Radius,self.MainCanvas1,"red")
            self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
            self.Xbar.config(command=self.MainCanvas1.xview)
            self.Ybar.config(command=self.MainCanvas1.yview)
            self.MainCanvas1.yview_moveto(0.0)
            self.MainCanvas1.xview_moveto(0.0)

            self.PDF_ADD_LIST.append(self.image)
            self.List_ADDED_Label.config(text=f"ADD = {len(self.PDF_ADD_LIST)}")
        else:
            msgbox.showerror("Error","The Perspective Points are missing")
        pass

    #----------PreviewScan Function----------
    def Preview_Scanning_FUNC(self,*args):
        if self.C1_cirlce in self.MainCanvas1.find_all():
            self.Points=self.MainCanvas1.coords(self.Point_Line)
            width=abs(self.Points[0]-self.Points[2])
            height=abs(self.Points[1]-self.Points[7])
            if self.Fixed_PDF_PAGE==False:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,width,height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            elif self.Fixed_PDF_PAGE==True:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,self.PDF_Width,self.PDF_Height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            image=Image.fromarray(scanimg).convert("RGB")
            image.thumbnail((900,600))
            
            # preview window
            self.Preview_Window=Toplevel()
            self.Preview_Window.config(highlightthickness=1,highlightbackground="yellow",highlightcolor="yellow")
            self.Preview_Window.config(bg="#082050")
            self.Preview_Window.geometry("+0+0")
            try:
                self.Preview_Window.wm_iconbitmap(self.APP_LOGO)
            except:
                pass
            for i in range(4):
                self.Preview_Window.columnconfigure(i,weight=1)
            self.Preview_Window.rowconfigure(0,weight=1)
            # label
            self.MainLabel4=Label(self.Preview_Window,bg="#00002c")
            self.MainLabel4.grid(row=0,column=0,columnspan=4,padx=1,pady=1)

            imgtk=ImageTk.PhotoImage(image=image)
            self.MainLabel4.config(image=imgtk)
            self.MainLabel4.image=imgtk

            # ok button
            Button(self.Preview_Window,borderwidth=1,relief=SOLID,bg="#6c09ed",fg="yellow",font=("arial",12,"bold"),activebackground="yellow",activeforeground="#6c09ed",text="OK",cursor="hand2",command=lambda : self.Preview_OK_FUNC(scanimg)).grid(row=1,column=0,padx=1,pady=1,sticky="nswe")
            Button(self.Preview_Window,borderwidth=1,relief=SOLID,bg="#6c09ed",fg="yellow",font=("arial",12,"bold"),activebackground="yellow",activeforeground="#6c09ed",text="ADD(➕)",cursor="hand2",command=lambda : self.Preview_ADD_FUNC(scanimg)).grid(row=1,column=1,padx=1,pady=1,sticky="nswe")
            Button(self.Preview_Window,borderwidth=1,relief=SOLID,bg="#6c09ed",fg="yellow",font=("arial",12,"bold"),activebackground="yellow",activeforeground="#6c09ed",text="Export",cursor="hand2",command=lambda : self.Preview_Export_FUNC(scanimg)).grid(row=1,column=2,padx=1,pady=1,sticky="nswe")
            Button(self.Preview_Window,borderwidth=1,relief=SOLID,bg="#6c09ed",fg="yellow",font=("arial",12,"bold"),activebackground="yellow",activeforeground="#6c09ed",text="Cancel",command=self.Preview_Window.destroy,cursor="hand2").grid(row=1,column=3,padx=1,pady=1,sticky="nswe")
            self.Preview_Window.bind("<Return>",lambda x : self.Preview_OK_FUNC(scanimg))
            self.Preview_Window.grab_set()
            self.Preview_Window.focus()
        else:
            msgbox.showerror("Error","The Perspective Points are missing")
        pass

    #----------PreviewScan OK Function----------
    def Preview_OK_FUNC(self,img):
        H=img.shape[0]
        W=img.shape[1]
        self.MainCanvas1.delete(ALL)
        self.image=Image.fromarray(img)
        self.opencvImage=np.array(self.image)

        imgtk=ImageTk.PhotoImage(self.image)
        self.MainCanvas1.create_image((0,0),image=imgtk,anchor="nw")
        self.MainCanvas1.image=imgtk
        self.MainCanvas1.yview_moveto(0.0)

        # polygon
        self.C1=[0,0]
        self.C2=[int(W),0]
        self.C3=[int(W),int(H)]
        self.C4=[0,int(H)]
                    
        self.Point_Line=self.MainCanvas1.create_polygon(self.C1,self.C2,self.C3,self.C4,fill="",outline="lime",width=2)

        self.C1_cirlce=self.create_circle(self.C1[0],self.C1[1],self.Circle_Radius,self.MainCanvas1,"red")
        self.C2_cirlce=self.create_circle(self.C2[0],self.C2[1],self.Circle_Radius,self.MainCanvas1,"red")
        self.C3_cirlce=self.create_circle(self.C3[0],self.C3[1],self.Circle_Radius,self.MainCanvas1,"red")
        self.C4_cirlce=self.create_circle(self.C4[0],self.C4[1],self.Circle_Radius,self.MainCanvas1,"red")
        self.MainCanvas1.config(xscrollcommand=self.Xbar.set,yscrollcommand=self.Ybar.set,scrollregion=self.MainCanvas1.bbox(ALL))
        self.Xbar.config(command=self.MainCanvas1.xview)
        self.Ybar.config(command=self.MainCanvas1.yview)
        self.Preview_Window.destroy()
        pass

    #----------PreviewScan ADD Function----------
    def Preview_ADD_FUNC(self,img):
        H=img.shape[0]
        W=img.shape[1]
        image=Image.fromarray(img).convert("RGB")
        try:
            dpi_x, dpi_y = self.image.info["dpi"]
        except KeyError:
            dpi_x, dpi_y = (self.wanted_dpi,self.wanted_dpi)
        self.image = self.image.resize((round(self.image.width*self.wanted_dpi/dpi_x), round(self.image.height*self.wanted_dpi/dpi_y)), resample=Image.LANCZOS)
        opencvImage=cv2.cvtColor(np.array(self.image),cv2.COLOR_BGR2RGB)

        self.PDF_ADD_LIST.append(image)
        self.List_ADDED_Label.config(text=f"ADD = {len(self.PDF_ADD_LIST)}")
        self.Preview_Window.destroy()
        pass

    #----------PreviewScan Export Function----------
    def Preview_Export_FUNC(self,img):
        img=cv2.cvtColor(img,cv2.COLOR_BGR2RGB)
        EXPORT.Export_IMAGE_FUNC(img,self.DataBase_FILE,self.Data_TABLE,self.Backup_Folder,self.Backup_Path,self.Save_Records)
        self.Preview_Window.destroy()
        pass

    #----------Scanned image to OCR----------
    def Adding_Scan_OCR_FUNC(self,*args):
        self.Image_Effect_Number=0
        if self.Image_Effect_Number==0 and self.C1_cirlce in self.MainCanvas1.find_all():
            self.Points=self.MainCanvas1.coords(self.Point_Line)
            width=abs(self.Points[0]-self.Points[2])
            height=abs(self.Points[1]-self.Points[7])
            self.scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,width,height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            img=Image.fromarray(self.scanimg)
            img.thumbnail((600,600))
            img=ImageTk.PhotoImage(image=img)
            self.MainLabel2.config(image=img)
            self.MainLabel2.image=img
            self.OCR_WIN_FUNC()
        else:
            msgbox.showwarning("warning","The OCR cannot be work on the Filters Image or Something went Wrong")
        pass

    #----------OCR Function----------
    def OCR_FUNC(self,*args):
        if self.MainLabel2.cget('image')!="":
            try:
                img=Process.Preprocess_img(self.scanimg)
                self.OCR_TextBox.delete(0.0,END)
                txt,boxes=OCR.OCR_PROCESS_FUNC(img,self.TESSERACT_PATH)
                if txt:
                    self.OCR_TextBox.insert(END,txt)
                    
                    H_img,W_img,_=self.scanimg.shape
                    self.boxes_img=cv2.cvtColor(self.scanimg,cv2.COLOR_RGB2BGR)

                    for b in boxes.splitlines():
                        b=b.split(" ")
                        x,y,w,h=int(b[1]),int(b[2]),int(b[3]),int(b[4])
                        cv2.rectangle(self.boxes_img,(x,H_img-y),(w,H_img-h),(255, 0, 128),1)

                    scanimg=cv2.cvtColor(self.boxes_img,cv2.COLOR_BGR2RGB)
                    img=Image.fromarray(scanimg)
                    img.thumbnail((600,600))
                    img=ImageTk.PhotoImage(image=img)
                    self.MainLabel2.config(image=img)
                    self.MainLabel2.image=img
            except:
                pass
        else:
            msgbox.showerror("Error","There is no Image for OCR Process")
        pass

    #----------Save the document as the PDF----------
    def Save_PDF_FUNC(self,*args):
        threading.Thread(target=EXPORT.Export_PDF_FUNC,args=[self.PDF_ADD_LIST,self.DataBase_FILE,self.Data_TABLE,self.Backup_Folder,self.Backup_Path,self.Save_Records]).start()
        pass

    #----------Save the document as the Image----------
    def Save_IMAGE_FUNC(self,*args):
        if self.C1_cirlce in self.MainCanvas1.find_all():
            self.Points=self.MainCanvas1.coords(self.Point_Line)
            width=abs(self.Points[0]-self.Points[2])
            height=abs(self.Points[1]-self.Points[7])
            if self.Fixed_PDF_PAGE==False:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,width,height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            elif self.Fixed_PDF_PAGE==True:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,self.PDF_Width,self.PDF_Height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            scanimg=cv2.cvtColor(scanimg,cv2.COLOR_BGR2RGB)
            EXPORT.Export_IMAGE_FUNC(scanimg,self.DataBase_FILE,self.Data_TABLE,self.Backup_Folder,self.Backup_Path,self.Save_Records)
        else:
            msgbox.showerror("Error","The Perspective Points are missing!")
        pass

    #----------Save the document as the Word----------
    def Save_OCR_Output(self,*args):
        data=self.OCR_TextBox.get(0.0,END)
        EXPORT.Export_WORD_FUNC(data,self.DataBase_FILE,self.Data_TABLE,self.Backup_Folder,self.Backup_Path,self.Save_Records)
        pass

    #----------Save The Add List as Images Thread----------
    def Save_ADDLIST_FUNC_Thread(self,*args):
        threading.Thread(target=self.Save_ADDLIST_FUNC).start()
        pass

    #----------Save The Add List as Images----------
    def Save_ADDLIST_FUNC(self,*args):
        EXPORT.Export_ADDLIST_FUNC(self.PDF_ADD_LIST,self.DataBase_FILE,self.Data_TABLE,self.Backup_Folder,self.Backup_Path,self.Save_Records)
        pass

    #----------Reset Everthing----------
    def Reset_ALL_FUNC(self,*args):
        asks=msgbox.askquestion("Reset","Do you want to Reset Everthing.")
        if asks=="yes":
            self.Org_List=[]
            self.PDF_ADD_LIST=[]
            self.title="DocScan"
            self.IMG_FORMAT=[".png",".jpeg",".jpg"]


            self.MainLabel1.config(image="")
            self.MainLabel2.config(image="")
            self.MainCanvas1.delete(ALL)
            self.OCR_TextBox.delete(0.0,END)
            self.ListBox_Combo.delete(0,END)
            self.ListBox_Combo.set("")
            self.Total_Label.config(text="")
            self.List_ADDED_Label.config(text="")
            self.Circle_Label.config(text="")
            self.StatusFrame.grid_forget()
            self.root.focus()

            self.Scan_Button.config(state=DISABLED)
            self.OCR_Button.config(state=DISABLED)
            self.Reset_Button.config(state=DISABLED)

            self.C1=[0,0]
            self.C2=[80,0]
            self.C3=[80,80]
            self.C4=[0,80]

            self.Poly=None

            self.ROTATION_List=[0,90,180,270,360]
            self.Rotate_Point=0

            self.Fixed_SIZE=750
            self.Size_Ratio=0.1
            self.Constant_Size=0.7
            self.fixed_ratio=self.Constant_Size
            self.Constant_size_Active=False

            self.Home_Active=True
            self.HOME_WIN_FUNC()
            self.HomeBody.grid(row=0,column=0,padx=0,pady=0,sticky="nswe")
            self.SCAN_Active=False
            self.ScanBody.grid_forget()
            self.OCR_Active=False
            self.OCRBody.grid_forget()
            self.Export_Active=False
            self.ExportBody.grid_forget()
            self.PDF_Active=False
            self.PDF_EDIT_Body.grid_forget()
            self.Status_Active=False
            self.SideTOOL_Active = True
            self.opencvImage=""
            self.Magnifying_Glass_Label.config(image="")

            self.Image_Effect_Number=0
            self.Fixed_PDF_PAGE=False
            self.PDF_Height=1648
            self.PDF_Width=1190
            
            self.DataBase_DIR=os.environ['USERPROFILE'].replace("\\","/")
            self.DataBase_FILE=f"{self.DataBase_DIR}/DocScan.db"
            self.Data_TABLE="Records"
            self.Backup_Folder="Backups_DocScan"
            self.backup_path_part1=os.path.dirname(self.DataBase_FILE).replace('\\','/')
            self.Backup_Path=f"{self.backup_path_part1}/{self.Backup_Folder}"

            self.Sharpen_NO=4
            self.Contrast_NO=2
            self.Thresh_NO=17
            self.Blut_NO=3
            self.Gamma_NO=0.5
            self.Bright_NO=50
            self.Image_Height=0
            self.Image_Width=0

            self.Total_PDF_Page_Label.config(text="")
            self.Current_PDF_Page_Label.config(text="")
            self.EDIT_PDF_LIST=[]
            self.PDF_EDIT_Pointer=0
            self.total_pdf_pages=0
            self.PDF_Reset_Active=False
            self.Size_PDF_Page_Label.config(text="")
            self.MainLabel_PDF.config(image="")

            self.root.title(self.title)
        pass

    #||||||||||||||||||||||||||||| To Edit List |||||||||||||||||||||||||||||

    #----------Edit Add List Window Function----------
    def Edit_LIST_WIN_FUNC(self,*args):
        if len(self.PDF_ADD_LIST)!=0:
            if self.Edit_WIN==True:
                self.Edit_List_WIN=Toplevel()
                self.Edit_List_WIN.title("Edit List")
                self.Edit_List_WIN.config(bg="#00002c")
                self.Edit_List_WIN.geometry("1083x567+92+38")
                self.Edit_List_WIN.protocol("WM_DELETE_WINDOW",self.Edit_WIN_DESTORY)
                try:
                    self.Edit_List_WIN.wm_iconbitmap(self.APP_LOGO)
                except:
                    pass
                # main label
                self.MainLabel3=Label(self.Edit_List_WIN,border=1,relief=SOLID,bg="#6c09ed")
                self.MainLabel3.pack(fill=BOTH,expand=True,padx=2,pady=2)
                # control frame
                self.Controls_Edit_Frame=Frame(self.Edit_List_WIN,bg="#6c09ed",border=1,relief=SOLID)
                for i in range(8):
                    self.Controls_Edit_Frame.columnconfigure(i,weight=1)
                # current image
                self.Current_Label_Edit=Label(self.Controls_Edit_Frame,text="Current Image = 1",font=("arial",12,"bold"),bg="#6c09ed",fg="yellow")
                self.Current_Label_Edit.grid(row=0,column=0,padx=2,pady=2,sticky="nswe")
                # Previous image
                self.Previous_Edit_Button=Button(self.Controls_Edit_Frame,text="◀ PREVIOUS",font=("arial",12,"bold"),cursor="hand2",bg="#00002c",fg="white",border=0,command=self.Previous_Image_Edit_FUNC)
                self.Previous_Edit_Button.grid(row=0,column=1,pady=2,padx=2,sticky="nswe")
                # Next image
                self.Next_Edit_Button=Button(self.Controls_Edit_Frame,text="NEXT ▶",font=("arial",12,"bold"),cursor="hand2",bg="#00002c",fg="white",border=0,command=self.Next_Image_Edit_FUNC)
                self.Next_Edit_Button.grid(row=0,column=2,pady=2,padx=2,sticky="nswe")
                # Replace
                self.Replace_Edit_Button=Button(self.Controls_Edit_Frame,text="REPLACE 🔄",font=("arial",12,"bold"),cursor="hand2",bg="#00002c",fg="white",border=0,command=self.Replace_Image_Edit_FUNC)
                self.Replace_Edit_Button.grid(row=0,column=3,pady=2,padx=2,sticky="nswe")
                # Remove image
                self.Remove_Edit_Button=Button(self.Controls_Edit_Frame,text="REMOVE ❌",font=("arial",12,"bold"),cursor="hand2",bg="#00002c",fg="white",border=0,command=self.Remove_Image_Edit_FUNC)
                self.Remove_Edit_Button.grid(row=0,column=4,pady=2,padx=2,sticky="nswe")
                # Insert image
                self.Insert_Edit_Button=Button(self.Controls_Edit_Frame,text="INSERT",font=("arial",12,"bold"),cursor="hand2",bg="#00002c",fg="white",border=0,command=self.Insert_Image_Edit_FUNC)
                self.Insert_Edit_Button.grid(row=0,column=5,pady=2,padx=2,sticky="nswe")
                # Export image
                self.Export_Edit_Button=Button(self.Controls_Edit_Frame,text="EXPORT",font=("arial",12,"bold"),cursor="hand2",bg="#00002c",fg="white",border=0,command=self.Save_EditList_Image_FUNC)
                self.Export_Edit_Button.grid(row=0,column=6,pady=2,padx=2,sticky="nswe")
                # reset the ADD list
                Button(self.Controls_Edit_Frame,text="RESET",font=("arial",12,"bold"),cursor="hand2",bg="#00002c",fg="white",border=0,command=lambda : [self.Reset_ADDED_LIST_FUNC(),self.Edit_WIN_DESTORY()]).grid(row=0,column=7,padx=2,pady=2,sticky="nswe")

                self.Controls_Edit_Frame.pack(fill=X,side=BOTTOM,pady=2,padx=2)
                self.First_Image_Edit_FUNC()
                self.Edit_WIN=False

                self.Edit_List_WIN.bind("<Right>",self.Next_Image_Edit_FUNC)
                self.Edit_List_WIN.bind("<Left>",self.Previous_Image_Edit_FUNC)
                self.Edit_List_WIN.mainloop()
        else:
            msgbox.showerror("Error","The Scan Image List is Empty")
        pass

    #----------Destroy Edit List Win Function----------
    def Edit_WIN_DESTORY(self,*args):
        self.Edit_List_WIN.destroy()
        self.Edit_WIN=True
        pass

    #----------Save Edit List Image Win Function----------
    def Save_EditList_Image_FUNC(self,*args):
        files=filedialog.asksaveasfilename(defaultextension=".png",filetypes=[("PNG","*.png"),("JPEG","*.jpg"),("TIFF","*.tiff"),("Bitmap","*.bmp")])
        if files!="":
            os.chdir(os.path.dirname(files))
            self.PDF_ADD_LIST[self.Edit_Pointer].save(f"{os.path.basename(files)}")
            if self.Save_Records==True:
                DATABASE.Insert_DATABASE(self.DataBase_FILE,f"{files}",self.Data_TABLE,self.Backup_Path)

                os.chdir(os.path.dirname(self.DataBase_FILE))
                if os.path.isdir(self.Backup_Folder):
                    os.chdir(self.Backup_Folder)
                    self.PDF_ADD_LIST[self.Edit_Pointer].save(f"{os.path.basename(files)}")
                else:
                    os.mkdir(self.Backup_Folder)
                    os.chdir(self.Backup_Folder)
                    self.PDF_ADD_LIST[self.Edit_Pointer].save(f"{os.path.basename(files)}")
            msgbox.showinfo("Successfull",f"The {files} has been Saved!")
            pass
        pass

    #----------Initial Edit Image Function----------
    def First_Image_Edit_FUNC(self,*args):
        self.Edit_Pointer=0
        data_img=np.array(self.PDF_ADD_LIST[0])
        newimg=Image.fromarray(data_img)
        newimg.thumbnail((600,500))
        newimg=ImageTk.PhotoImage(image=newimg)
        self.MainLabel3.config(image=newimg)
        self.MainLabel3.image=newimg
        pass

    #----------Next Edit Image Function----------
    def Next_Image_Edit_FUNC(self,*args):
        x=len(self.PDF_ADD_LIST)
        self.Edit_Pointer=self.Edit_Pointer+1
        if self.Edit_Pointer<x:
            data_img=np.array(self.PDF_ADD_LIST[self.Edit_Pointer])
            newimg=Image.fromarray(data_img)
            newimg.thumbnail((600,500))
            newimg=ImageTk.PhotoImage(image=newimg)
            self.MainLabel3.config(image=newimg)
            self.MainLabel3.image=newimg
            self.Current_Label_Edit.config(text=f"Current Image = {self.Edit_Pointer+1}")
        else:
            self.Edit_Pointer=self.Edit_Pointer-1
        pass

    #----------Previous Edit Image Function----------
    def Previous_Image_Edit_FUNC(self,*args):
        x=len(self.PDF_ADD_LIST)
        self.Edit_Pointer=self.Edit_Pointer-1
        if self.Edit_Pointer>=0:
            data_img=np.array(self.PDF_ADD_LIST[self.Edit_Pointer])
            newimg=Image.fromarray(data_img)
            newimg.thumbnail((600,500))
            newimg=ImageTk.PhotoImage(image=newimg)
            self.MainLabel3.config(image=newimg)
            self.MainLabel3.image=newimg
            self.Current_Label_Edit.config(text=f"Current Image = {self.Edit_Pointer+1}")
        else:
            self.Edit_Pointer=self.Edit_Pointer+1
        pass

    #----------Remove Edit Image Function----------
    def Remove_Image_Edit_FUNC(self,*args):
        if len(self.PDF_ADD_LIST)>1:
            asks=msgbox.askquestion("Remove",f"Do You want to Remove The Image no {self.Edit_Pointer+1} from the List!")
            if asks=="yes":
                del self.PDF_ADD_LIST[self.Edit_Pointer]
                self.List_ADDED_Label.config(text=f"ADD = {len(self.PDF_ADD_LIST)}")
                self.MainLabel3.config(image="")
                msgbox.showinfo("Successfull","The Image has been Removed!")
                self.Edit_List_WIN.focus()
            else:
                self.Edit_List_WIN.focus()
        else:
            self.Reset_ADDED_LIST_FUNC()
            self.Edit_List_WIN.destroy()
            self.Edit_WIN=True
        pass

    #----------Replace Edit Image Function----------
    def Replace_Image_Edit_FUNC(self,*args):
        asks=msgbox.askquestion("Replace",f"Do you want to replace this image with another index number = {self.Edit_Pointer+1}")
        if asks=="yes":
            self.Points=self.MainCanvas1.coords(self.Point_Line)
            width=abs(self.Points[0]-self.Points[2])
            height=abs(self.Points[1]-self.Points[7])
            if self.Fixed_PDF_PAGE==False:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,width,height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            elif self.Fixed_PDF_PAGE==True:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,self.PDF_Width,self.PDF_Height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            img=Image.fromarray(scanimg)
            self.PDF_ADD_LIST[self.Edit_Pointer]=img
            self.List_ADDED_Label.config(text=f"ADD = {len(self.PDF_ADD_LIST)}")
            msgbox.showinfo("Replace","The Image Has Been Replaced")
            self.Edit_List_WIN.focus()
        else:
            self.Edit_List_WIN.focus()
        pass

    #----------Insert Edit Image Function----------
    def Insert_Image_Edit_FUNC(self,*args):
        asks=msgbox.askquestion("Insert",f"Do you want to Insert this image here at index number = {self.Edit_Pointer+1}")
        if asks=="yes":
            self.Points=self.MainCanvas1.coords(self.Point_Line)
            width=abs(self.Points[0]-self.Points[2])
            height=abs(self.Points[1]-self.Points[7])
            if self.Fixed_PDF_PAGE==False:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,width,height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            elif self.Fixed_PDF_PAGE==True:
                scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage,self.PDF_Width,self.PDF_Height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
            img=Image.fromarray(scanimg)

            self.PDF_ADD_LIST.insert(self.Edit_Pointer,img)
            self.List_ADDED_Label.config(text=f"ADD = {len(self.PDF_ADD_LIST)}")
            msgbox.showinfo("Insert","The Image Has Been Inserted")
            self.Edit_List_WIN.focus()
        else:
            self.Edit_List_WIN.focus()
        pass

    #||||||||||||||||||||||||||||| To WebCam |||||||||||||||||||||||||||||

    #----------WebCam Window Function----------
    def Webcam_WIN_FUNC(self,*args):
        self.Webcam_Win=Toplevel()
        self.Webcam_Win.title("WebCam")
        self.Webcam_Win.geometry("+0+0")
        self.Webcam_Win.config(bg="#6c09ed")
        self.Webcam_Win.resizable(0,0)
        try:
            self.Webcam_Win.wm_iconbitmap(self.APP_LOGO)
        except:
            pass
        # label 
        Label(self.Webcam_Win,text="WebCam",font=("arial",20,"bold"),fg="black",bg="#6c09ed").grid(row=0,column=0,columnspan=5,padx=2,pady=2,sticky="nswe")
        Label(self.Webcam_Win,text="Enter the WebCam Pin or URL",font=("arial",12,"bold"),fg="white",bg="#6c09ed").grid(row=1,column=0,pady=2,padx=2,sticky="nswe")
        # entry box
        self.WebCam_Value=StringVar()
        E1=ttk.Entry(self.Webcam_Win,font=("arial",12,"bold"),textvariable=self.WebCam_Value)
        E1.grid(row=1,column=1,columnspan=2,padx=2,pady=2,sticky="nswe")
        E1.focus()
        self.WebCam_Value.set("0")
        # button
        self.WebStart_Button=Button(self.Webcam_Win,text="Start",cursor="hand2",font=("arial",12),bg="#00002c",fg="white",border=1,relief=SOLID,command=self.Starting_WebCam_Thread_FUNC)
        self.WebStart_Button.grid(row=2,column=0,pady=2,padx=2,sticky="nswe")
        Button(self.Webcam_Win,text="Stop",font=("arial",12),cursor="hand2",bg="#00002c",fg="white",border=1,relief=SOLID,command=self.Stop_WebCam_FUNC).grid(row=2,column=1,pady=2,padx=2,sticky="nswe")
        Button(self.Webcam_Win,text="Capture",font=("arial",12),cursor="hand2",bg="#00002c",fg="white",border=1,relief=SOLID,command=self.Capture_WebCam_Image_FUNC).grid(row=2,column=2,pady=2,padx=2,sticky="nswe")
        # label capture
        self.Capture_Label=Label(self.Webcam_Win,font=("arial",12),bg="#6c09ed",fg="yellow")
        self.Capture_Label.grid(row=3,column=0,padx=2,pady=2,sticky="nswe")
        self.Webcam_Win.bind("<Return>",self.Capture_WebCam_Image_FUNC)
        self.Webcam_Win.grab_set()
        self.Webcam_Win.focus()
        pass

    #----------Start WebCam Function----------
    def Start_WebCam_Image_FUNC(self,*args):
        if self.WebCam_Value.get()!="":
            self.WebStart_Button.config(state=DISABLED)
            if self.WebCam_Value.get().isdigit()==True:
                camera=int(self.WebCam_Value.get())
                cap=cv2.VideoCapture(camera,cv2.CAP_DSHOW)
            else:
                camera=str(self.WebCam_Value.get())
                cap=cv2.VideoCapture(camera)

            self.Webcam_On=True
            # cap.set(cv2.CAP_PROP_BUFFERSIZE, 2)
            while self.Webcam_On:
                checks,self.WebRead=cap.read()
                if checks==True:
                    self.WebRead=cv2.resize(self.WebRead,(0,0),fx=1.3,fy=1.3,interpolation=cv2.INTER_AREA)
                    img=cv2.cvtColor(self.WebRead.copy(),cv2.COLOR_BGR2RGB)
                    img=Image.fromarray(img.copy())
                    img.thumbnail((int(self.MainLabel1.winfo_width()-20),int(self.MainLabel1.winfo_height()-20)))
                    # img=img.resize((int(self.MainLabel1.winfo_width()-20),int(self.MainLabel1.winfo_height()-20)),Image.ANTIALIAS)
                    img=ImageTk.PhotoImage(image=img)
                    self.MainLabel1.config(image=img)
                    self.MainLabel1.image=img
                elif checks==False:
                    msgbox.showwarning("warning","Unable to read the Frames")
                    self.WebStart_Button.config(state=NORMAL)
                    self.Stop_WebCam_FUNC()
                    cap.release()
                    break
            self.MainLabel1.config(image="")
            cap.release()
            pass
        else:
            msgbox.showerror("Error","There is no Camera")
        pass

    #----------Start WebCam Thread Function----------
    def Starting_WebCam_Thread_FUNC(self,*args):
        threading.Thread(target=self.Start_WebCam_Image_FUNC,daemon=True).start()
        pass

    #----------Stop WebCam Function----------
    def Stop_WebCam_FUNC(self,*args):
        if self.Webcam_On==True:
            self.Webcam_On=False
            self.MainLabel1.config(image="")
            if self.insert_urls!="":
                if len(self.Org_List)!=0 and self.Status_Active==True:
                    self.ListBox_Combo["values"]=self.Org_List
                    indexno=self.ListBox_Combo.current()
                    self.ListBox_Combo.set(self.Org_List[0])
                elif len(self.Org_List)!=0 and self.Status_Active==False:
                    self.Display_Status_FUNC(self.Org_List)
                    indexno=self.ListBox_Combo.current()
                    self.ListBox_Combo.set(self.Org_List[0])
                    self.Status_Active=True
                self.Combobox_Change_FUNC()
            self.WebStart_Button.config(state=NORMAL)
            self.Capture_Label.config(text="")
        else:
            msgbox.showwarning("Warning","The Camera never started")
        pass

    #----------WebCam Image Capture Function----------
    def Capture_WebCam_Image_FUNC(self,*args):
        if self.Webcam_On==True:
            os.chdir(self.DataBase_DIR)
            if os.path.isdir(self.WebCam_Folder_Name):
                os.chdir(self.WebCam_Folder_Name)
                x=datetime.datetime.now()
                cv2.imwrite(f"DocSan Image {self.WebCam_Capture_NO}-{x.strftime('%H')}-{x.strftime('%M')}-{x.strftime('%S')}.png",self.WebRead)

                self.insert_urls=os.path.abspath(f"DocSan Image {self.WebCam_Capture_NO}-{x.strftime('%H')}-{x.strftime('%M')}-{x.strftime('%S')}.png")
                self.Org_List.append(self.insert_urls)
                self.WebCam_Capture_NO=self.WebCam_Capture_NO+1
                self.Capture_Label.config(text=os.path.basename(self.insert_urls))
                pass
            else:
                os.mkdir(self.WebCam_Folder_Name)
                os.chdir(self.WebCam_Folder_Name)
                x=datetime.datetime.now()
                cv2.imwrite(f"DocSan Image {self.WebCam_Capture_NO}-{x.strftime('%H')}-{x.strftime('%M')}-{x.strftime('%S')}.png",self.WebRead)

                self.insert_urls=os.path.abspath(f"DocSan Image {self.WebCam_Capture_NO}-{x.strftime('%H')}-{x.strftime('%M')}-{x.strftime('%S')}.png")
                self.Org_List.append(self.insert_urls)
                self.WebCam_Capture_NO=self.WebCam_Capture_NO+1
                self.Capture_Label.config(text=os.path.basename(self.insert_urls))
        else:
            msgbox.showerror("Error","There is no Frame")
        pass

    #----------Shortcut key binding Function----------
    def Shortcut_Keys_Win_FUNC(self,*args):
        self.Key_WIN=Toplevel()
        self.Key_WIN.title("Shortcut Keys")
        self.Key_WIN.config(bg="#6c09ed")
        self.Key_WIN.geometry("+0+0")
        self.Key_WIN.resizable(0,0)
        try:
            self.Key_WIN.wm_iconbitmap(self.APP_LOGO)
        except:
            pass
        # scrollbars
        self.key_Ybar=ttk.Scrollbar(self.Key_WIN,orient=VERTICAL)
        self.key_Ybar.pack(fill=Y,side=RIGHT)
        # canvas
        self.Key_Canvas=Canvas(self.Key_WIN,borderwidth=1,relief=SOLID,bg="#6c09ed",highlightthickness=0,yscrollcommand=self.key_Ybar.set)
        self.Key_Canvas.pack(fill=BOTH,expand=True)
        # frame
        self.Key_Frame=Frame(self.Key_Canvas,bg="#6c09ed")
        self.Key_Frame.pack(fill=BOTH,expand=True)
        self.Key_Canvas.create_window((0,0),window=self.Key_Frame,anchor="nw")

        Label(self.Key_Frame,text=f"Key",font=("Calibri",12,"bold"),fg="yellow",bg="#4d00aa",anchor="nw",border=1,relief=SOLID,padx=2,pady=2).grid(row=0,column=0,padx=5,pady=5,sticky="nswe")
        Label(self.Key_Frame,text=f"description",font=("Calibri",12,"bold"),fg="yellow",bg="#4d00aa",anchor="nw",border=1,relief=SOLID,padx=2,pady=2).grid(row=0,column=1,padx=5,pady=5,sticky="nswe")
        for i in range(len(self.Shortcut_Patterns)):
            Label(self.Key_Frame,text=self.Shortcut_Patterns[i],font=("Calibri",12,"bold"),fg="yellow",bg="#00002c",anchor="nw",border=1,relief=SOLID,padx=2,pady=2).grid(row=i+1,column=0,padx=5,pady=5,sticky="nswe")
            Label(self.Key_Frame,text=self.Shortcut_Desc[i],font=("Calibri",12,"bold"),fg="yellow",bg="#00002c",anchor="nw",border=1,relief=SOLID,padx=2,pady=2).grid(row=i+1,column=1,padx=5,pady=5,sticky="nswe")
        self.Key_Canvas.config(scrollregion=self.Key_Canvas.bbox(ALL))
        self.key_Ybar.config(command=self.Key_Canvas.yview)
        self.Key_Frame.bind("<MouseWheel>",self.Scroll_Keyboard)
        self.Key_Canvas.bind("<MouseWheel>",self.Scroll_Keyboard)
        self.Key_WIN.grab_set()
        self.Key_WIN.focus()
        pass

    #----------Scroll Key window Function----------
    def Scroll_Keyboard(self,e):
        self.Key_Canvas.yview_scroll(int(-1/e.delta*120),UNITS)
        self.Key_Canvas.config(scrollregion=self.Key_Canvas.bbox(ALL))
        pass

    #----------Full Screen Function----------
    def FullScreen_FUNC(self,*args):
        if self.FullScreen_Active==True:
            self.FullScreen_Active=False
            self.root.attributes("-fullscreen", False)
            self.FullScreen_Button.config(text="Full Screen \u26F6")
            self.root.focus()
        elif self.FullScreen_Active==False:
            self.FullScreen_Active=True
            self.root.attributes("-fullscreen", True)
            self.FullScreen_Button.config(text="Normal Screen")
            self.root.focus()
        pass

    #----------Full Screen Keyboard Function----------
    def FullScreen_Keyboard_FUNC(self,*args):
        if self.FullScreen_Active==True:
            self.FullScreen_Active=False
            self.root.attributes("-fullscreen", False)
            self.root.focus()
        elif self.FullScreen_Active==False:
            self.FullScreen_Active=True
            self.root.attributes("-fullscreen", True)
            self.root.focus()
        pass

    #----------Help Window Function----------
    def Help_Window_FUNC(self,*args):
        self.Help_WIN=Toplevel()
        self.Help_WIN.title("Help")
        self.Help_WIN.config(bg="#6c09ed")
        self.Help_WIN.geometry(f"+0+0")
        self.Help_WIN.resizable(0,0)
        try:
            self.Help_WIN.wm_iconbitmap(self.APP_LOGO)
        except:
            pass
        L1=LabelFrame(self.Help_WIN,text="Documentation",font=("arial",25,"bold"),bg="#00002c",fg="white",relief=SOLID,highlightthickness=2,highlightbackground="yellow",highlightcolor="yellow")
        L1.columnconfigure(0,weight=1)
        # getting started
        Label(L1,text="Getting Started -",font=("arial",15,"bold","italic"),bg="#00002c",fg="yellow",anchor="nw").grid(row=0,column=0,padx=2,pady=2,sticky="nswe")
        # Text
        T1=Text(L1,font=("Calibri",15,"bold"),bg="yellow",fg="black",borderwidth=1,relief=SOLID,height=7,wrap=WORD,selectbackground="red",cursor="arrow")
        T1.grid(row=1,column=0,padx=2,pady=2,sticky="nswe")

        T1.insert(END,getting_started_Text.strip())
        T1.config(state=DISABLED)
        # Steps
        Label(L1,text="Steps -",font=("arial",15,"bold","italic"),bg="#00002c",fg="yellow",anchor="nw").grid(row=2,column=0,padx=2,pady=2,sticky="nswe")
        # Text
        T2=Text(L1,font=("Calibri",15,"bold"),bg="yellow",fg="black",borderwidth=1,relief=SOLID,height=12,wrap=WORD,selectbackground="red",cursor="arrow")
        T2.grid(row=3,column=0,padx=2,pady=2,sticky="nswe")
        T2.insert(END,Steps_Text.strip())
        T2.config(state=DISABLED)

        L1.pack(fill=BOTH,expand=True,padx=6,pady=6)
        self.Help_WIN.grab_set()
        self.Help_WIN.focus()
        pass

    #----------Exit Function----------
    def Exit_FUNC(self,*args):
        if len(self.Org_List)!=0 or len(self.PDF_ADD_LIST)!=0 or len(self.EDIT_PDF_LIST)!=0:
            x=msgbox.askquestion("Exit","Do you want to Exit")
            if x=="yes":
                gc.collect()
                self.root.destroy()
        else:
            self.root.destroy()

    #||||||||||||||||||||||||||||| To PDF Edit |||||||||||||||||||||||||||||

    #----------PDF Thread Function----------
    def Import_PDF_Thread_FUNC(self,*args):
        threading.Thread(target=self.Import_PDF_FUNC,daemon=True).start()
        pass

    #----------PDF Import Function----------
    def Import_PDF_FUNC(self,*args):
        files=filedialog.askopenfilename(title="PDF Import",defaultextension=".pdf",filetypes=[("PDF File","*.pdf")])
        if files!="":
            # try:
                self.Total_PDF_Page_Label.config(text="")
                self.Current_PDF_Page_Label.config(text="")
                self.Size_PDF_Page_Label.config(text="")
                self.EDIT_PDF_LIST=[]
                self.PDF_EDIT_Pointer=0
                self.total_pdf_pages=0
                self.PDF_Reset_Active=False
                self.MainLabel_PDF.config(image="")
                doc = fitz.open(files)
                self.total_pdf_pages=int(doc.page_count)
                self.Current_PDF_Page_Label.config(text=f"Total Page = {self.total_pdf_pages}")
                self.PDF_Reset_Active=True
                dpis = (200/72)
                if self.total_pdf_pages>0 and self.total_pdf_pages<1000:
                    self.PDF_EDIT_Pointer=0

                    # inital page display
                    firstpage = doc.load_page(0)
                    pix = firstpage.get_pixmap(matrix=fitz.Matrix(dpis,dpis))
                    temp = Image.frombuffer('RGB', [pix.width, pix.height], pix.samples,"raw", "RGB", 0,1)
                    H,W = temp.size
                    temp.thumbnail((int(self.MainLabel_PDF.winfo_width()-10),int(self.MainLabel_PDF.winfo_height()-10)),Image.ANTIALIAS)
                    img=ImageTk.PhotoImage(temp)
                    self.MainLabel_PDF.config(image=img)
                    self.MainLabel_PDF.image=img
                    self.Size_PDF_Page_Label.config(text=f"Height:{W}\nWidth:{H}")
                    self.PDF_INSERT_H,self.PDF_INSERT_W=H,W
                    self.PDF_Edit_Import_Button.config(state=DISABLED)
                    self.PDF_Edit_Insert_Button.config(state=DISABLED)
                    self.PDF_Edit_Remove_Button.config(state=DISABLED)
                    self.PDF_Edit_Export_Button.config(state=DISABLED)
                    self.List_PDF_Save_Button.config(state=DISABLED)

                    for page in doc:
                        if self.PDF_Reset_Active==True:
                            pix = page.get_pixmap(matrix=fitz.Matrix(dpis,dpis))
                            self.EDIT_PDF_LIST.append(Image.fromarray(np.frombuffer(pix.samples,dtype=np.uint8).reshape(pix.h, pix.w, pix.n)).convert("RGB"))
                            self.Total_PDF_Page_Label.config(text=f"{self.PDF_EDIT_Pointer+1} / {len(self.EDIT_PDF_LIST)}")
                            # time.sleep(0.0001)
                        else:
                            self.Current_PDF_Page_Label.config(text="")
                            self.Size_PDF_Page_Label.config(text="")
                            self.PDF_EDIT_Pointer=0
                            self.total_pdf_pages=0
                            self.PDF_Reset_Active=False
                            self.EDIT_PDF_LIST=[]
                            self.Total_PDF_Page_Label.config(text="")
                            self.MainLabel_PDF.config(image="")
                            break
                    self.PDF_Edit_Import_Button.config(state=NORMAL)
                    self.PDF_Edit_Insert_Button.config(state=NORMAL)
                    self.PDF_Edit_Remove_Button.config(state=NORMAL)
                    self.PDF_Edit_Export_Button.config(state=NORMAL)
                    self.List_PDF_Save_Button.config(state=NORMAL)
                    gc.collect()
                else:
                    self.Total_PDF_Page_Label.config(text="")
                    self.Current_PDF_Page_Label.config(text="")
                    self.EDIT_PDF_LIST=[]
                    self.PDF_EDIT_Pointer=0
                    self.total_pdf_pages=0
                    self.PDF_Reset_Active=False
                    self.root.focus()
                    self.Size_PDF_Page_Label.config(text="")
                    self.MainLabel_PDF.config(image="")
                    msgbox.showwarning("Warning","The File size is Huge!")
            # except Exception as e:
            #     msgbox.showerror("Error",f"{e}")
        pass

    #----------Next PDF Page Function----------
    def Next_PDF_FUNC(self,*args):
        x=self.PDF_EDIT_Pointer+1
        if x<len(self.EDIT_PDF_LIST):
            self.PDF_EDIT_Pointer=x
            temp=self.EDIT_PDF_LIST[self.PDF_EDIT_Pointer].copy()
            H,W=temp.size
            self.PDF_INSERT_H,self.PDF_INSERT_W=H,W
            self.Size_PDF_Page_Label.config(text=f"Height:{W}\nWidth:{H}")
            temp.thumbnail((int(self.MainLabel_PDF.winfo_width()-10),int(self.MainLabel_PDF.winfo_height()-10)),Image.ANTIALIAS)
            img=ImageTk.PhotoImage(temp)
            self.MainLabel_PDF.config(image=img)
            self.MainLabel_PDF.image=img
            self.Total_PDF_Page_Label.config(text=f"{self.PDF_EDIT_Pointer+1} / {len(self.EDIT_PDF_LIST)}")

    #----------Previous PDF Page Function----------
    def Previous_PDF_FUNC(self,*args):
        x=self.PDF_EDIT_Pointer-1
        if x>=0:
            self.PDF_EDIT_Pointer=x
            temp=self.EDIT_PDF_LIST[self.PDF_EDIT_Pointer].copy()
            H,W=temp.size
            self.PDF_INSERT_H,self.PDF_INSERT_W=H,W
            self.Size_PDF_Page_Label.config(text=f"Height:{W}\nWidth:{H}")
            temp.thumbnail((int(self.MainLabel_PDF.winfo_width()-10),int(self.MainLabel_PDF.winfo_height()-10)),Image.ANTIALIAS)
            img=ImageTk.PhotoImage(temp)
            self.MainLabel_PDF.config(image=img)
            self.MainLabel_PDF.image=img
            self.Total_PDF_Page_Label.config(text=f"{self.PDF_EDIT_Pointer+1} / {len(self.EDIT_PDF_LIST)}")
        pass

    #----------Insert PDF Page Function----------
    def Insert_PDF_FUNC(self,*args):
        if len(self.EDIT_PDF_LIST)!=0:
            files=filedialog.askopenfilename(defaultextension=".png",filetypes=[("PNG","*.png"),("JPEG","*.jpg")])
            if files!="":
                img=Image.open(files).convert("RGB")
                img=img.resize((self.PDF_INSERT_H,self.PDF_INSERT_W),Image.LANCZOS)
                self.EDIT_PDF_LIST.insert(self.PDF_EDIT_Pointer,img)
                msgbox.showinfo("Successful",f"The Image has been Inserted at {self.PDF_EDIT_Pointer+1}")
        pass

    #----------Remove PDF Page Function----------
    def Remove_PDF_FUNC(self,*args):
        if len(self.EDIT_PDF_LIST)!=0:
            asks=msgbox.askquestion("Remove","Do you really want to remove this page!")
            if asks=="yes":
                del self.EDIT_PDF_LIST[self.PDF_EDIT_Pointer]
                msgbox.showinfo("Successful",f"The Image has been removed at {self.PDF_EDIT_Pointer+1}")
        pass

    #----------Reset PDF Page Function----------
    def Reset_PDF_FUNC(self,*args):
        asks=msgbox.askquestion("Reset","Do you want to reset")
        if asks=="yes":
            self.Total_PDF_Page_Label.config(text="")
            self.Current_PDF_Page_Label.config(text="")
            self.EDIT_PDF_LIST=[]
            self.PDF_EDIT_Pointer=0
            self.total_pdf_pages=0
            self.PDF_Reset_Active=False
            self.root.focus()
            self.Size_PDF_Page_Label.config(text="")
            self.MainLabel_PDF.config(image="")
            gc.collect()
        pass

    #----------Export PDF Page Function----------
    def Export_PDF_EDIT_FUNC(self,*args):
        threading.Thread(target=EXPORT.Export_PDF_FUNC,args=[self.EDIT_PDF_LIST,self.DataBase_FILE,self.Data_TABLE,self.Backup_Folder,self.Backup_Path,self.Save_Records],daemon=True).start()
        pass

    #----------Export Image Page Function----------
    def Export_PDF_Image_EDIT_FUNC(self,*args):
        if len(self.EDIT_PDF_LIST)!=0:
            files=filedialog.asksaveasfilename(defaultextension=".png",filetypes=[("PNG","*.png"),("JPEG","*.jpg"),("TIFF","*.tiff"),("Bitmap","*.bmp")])
            if files!="":
                os.chdir(os.path.dirname(files))
                self.EDIT_PDF_LIST[self.PDF_EDIT_Pointer].save(f"{os.path.basename(files)}")
                if self.Save_Records==True:
                    DATABASE.Insert_DATABASE(self.DataBase_FILE,f"{files}",self.Data_TABLE,self.Backup_Path)
                if self.Save_Records==True:
                    os.chdir(os.path.dirname(self.DataBase_FILE))
                    if os.path.isdir(self.Backup_Folder):
                        os.chdir(self.Backup_Folder)
                        self.EDIT_PDF_LIST[self.PDF_EDIT_Pointer].save(f"{os.path.basename(files)}")
                    else:
                        os.mkdir(self.Backup_Folder)
                        os.chdir(self.Backup_Folder)
                        self.EDIT_PDF_LIST[self.PDF_EDIT_Pointer].save(f"{os.path.basename(files)}")
                msgbox.showinfo("Successfull",f"The {files} has been Saved!")
        else:
            msgbox.showerror("Error","Something went wrong!")
        pass

    #----------Export PDF List Page Thread Function----------
    def Export_PDF_EDIT_LIST_Thread_FUNC(self,*args):
        threading.Thread(target=self.Export_PDF_EDIT_LIST_FUNC,daemon=True).start()
        pass

    #----------Export PDF List Page Function----------
    def Export_PDF_EDIT_LIST_FUNC(self,*args):
        EXPORT.Export_ADDLIST_FUNC(self.EDIT_PDF_LIST,self.DataBase_FILE,self.Data_TABLE,self.Backup_Folder,self.Backup_Path,self.Save_Records)
        pass

    #----------Insert Scan to PDF Page Function----------
    def Scan2PDF_FUNC(self,*args):
        if self.C1_cirlce in self.MainCanvas1.find_all() and self.total_pdf_pages!=0:
            if(msgbox.askquestion("Insert","Do you want to Insert This Image in PDF")=="yes"):
                self.Points=self.MainCanvas1.coords(self.Point_Line)
                width=abs(self.Points[0]-self.Points[2])
                height=abs(self.Points[1]-self.Points[7])
                if self.Fixed_PDF_PAGE==False:
                    scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage.copy(),width,height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
                elif self.Fixed_PDF_PAGE==True:
                    scanimg=Scanning.WrapPerspective_FUNC(self.opencvImage.copy(),self.PDF_Width,self.PDF_Height,self.C1,self.C2,self.C3,self.C4,self.Image_Effect_Number,self.Gamma_NO,self.Sharpen_NO,self.Contrast_NO,self.Thresh_NO,self.Blut_NO,self.Bright_NO)
                img=Image.fromarray(scanimg)
                img=img.resize((self.PDF_INSERT_H,self.PDF_INSERT_W),Image.ANTIALIAS)
                self.EDIT_PDF_LIST.insert(self.PDF_EDIT_Pointer,img)
                msgbox.showinfo("Successful",f"The Image has been Inserted at {self.PDF_EDIT_Pointer+1}")
        else:
            msgbox.showwarning("Warning","There is no PDF!")
        pass

    #----------Rotate PDF Page Function----------
    def Rotate_PDF_IMAGE_FUNC(self,*args):
        if len(self.EDIT_PDF_LIST)!=0:
            temp=self.EDIT_PDF_LIST[self.PDF_EDIT_Pointer].copy()
            temp = temp.rotate(90,Image.ANTIALIAS,expand = 1)
            self.EDIT_PDF_LIST[self.PDF_EDIT_Pointer]=temp.copy()
            temp.thumbnail((int(self.MainLabel_PDF.winfo_width()-10),int(self.MainLabel_PDF.winfo_height()-10)),Image.ANTIALIAS)
            temp = ImageTk.PhotoImage(temp)
            self.MainLabel_PDF.config(image="")
            self.MainLabel_PDF.config(image=temp)
            self.MainLabel_PDF.image=temp
        else:
            msgbox.showerror("Error","There is no PDF Open")
    pass

############################################################### Process Class ###############################################################

class Process:
    #----------Pre Processing the Image for OCR----------
    def Preprocess_img(img):
        # img=cv2.bitwise_not(img)
        grayimg=cv2.cvtColor(img,cv2.COLOR_BGR2GRAY)
        thresh,thresh_img=cv2.threshold(grayimg,0,255,cv2.THRESH_OTSU)
        inverts=255-thresh_img
        return inverts
    
    #----------Effects on the Image----------
    def Image_Effect_FUNC(img,n,gammas=0.7,sharpen=4,contracts=2,thresh_C=17,blur_n=3,brights=50):
        # Original image
        if n==0:
            return img
        # gray scale image
        elif n==1:
            return cv2.cvtColor(img,cv2.COLOR_BGR2GRAY)
        # bright image
        elif n==2:
            hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
            h, s, v = cv2.split(hsv)

            lim = 255 - brights
            v[v > lim] = 255
            v[v <= lim] = brights+v[v <= lim]

            final_hsv = cv2.merge((h, s, v))
            imgbright = cv2.cvtColor(final_hsv, cv2.COLOR_HSV2BGR)
            return imgbright
        # Sharphen image
        elif n==3:
            from_img=Image.fromarray(img)
            new_img=ImageEnhance.Sharpness(from_img).enhance(sharpen)
            cv_img=np.array(new_img)
            return cv_img
        # Red Image
        elif n==4:
            r,g,b=cv2.split(img)
            zeros=np.zeros(img.shape[:2],dtype="uint8")
            return cv2.merge([r,zeros,zeros])
        # Blue Image
        elif n==5:
            r,g,b=cv2.split(img)
            zeros=np.zeros(img.shape[:2],dtype="uint8")
            return cv2.merge([zeros,zeros,b])
        # Green Image
        elif n==6:
            r,g,b=cv2.split(img)
            zeros=np.zeros(img.shape[:2],dtype="uint8")
            return cv2.merge([zeros,g,zeros])
        # Yellow Image
        elif n==7:
            r,g,b=cv2.split(img)
            zeros=np.zeros(img.shape[:2],dtype="uint8")
            return cv2.merge([g,g,zeros])
        # gamma
        elif n==8:
            invGamma = 1.0 / gammas
            table = np.array([((i / 255.0) ** invGamma) * 255
                for i in np.arange(0, 256)]).astype("uint8")
            return cv2.LUT(img, table)
        # contrast
        elif n==9:
            from_img=Image.fromarray(img)
            new_img=ImageEnhance.Contrast(from_img).enhance(contracts)
            cv_img=np.array(new_img)
            return cv_img
        # Binary
        elif n==10:
            grayimg=cv2.cvtColor(img,cv2.COLOR_BGR2GRAY)
            kernel = np.ones((2, 2), np.uint8)
            grayimg = cv2.GaussianBlur(grayimg, (5, 5), 0)
            thresh_img=cv2.adaptiveThreshold(grayimg,255,cv2.ADAPTIVE_THRESH_MEAN_C,cv2.THRESH_BINARY,21,thresh_C)
            # kernel=np.ones((1,1))
            # dial_img=cv2.dilate(thresh_img,kernel,iterations=3)
            # erode_img=cv2.erode(dial_img,kernel,iterations=1)
            return thresh_img
        # Binary Invert
        elif n==11:
            grayimg=cv2.cvtColor(img,cv2.COLOR_BGR2GRAY)
            kernel = np.ones((2, 2), np.uint8)
            grayimg = cv2.GaussianBlur(grayimg, (5, 5), 0)
            thresh_img=cv2.adaptiveThreshold(grayimg,255,cv2.ADAPTIVE_THRESH_MEAN_C,cv2.THRESH_BINARY,21,thresh_C)
            thresh_img=255-thresh_img
            # kernel=np.ones((1,1))
            # dial_img=cv2.dilate(thresh_img,kernel,iterations=3)
            # erode_img=cv2.erode(dial_img,kernel,iterations=1)
            return thresh_img
        # Blur
        elif n==12:
            blur_img=cv2.medianBlur(img,blur_n)
            return blur_img
        # sketch
        elif n==13:
            gray_img=cv2.cvtColor(img,cv2.COLOR_BGR2GRAY)
            blur_img=cv2.GaussianBlur(gray_img,(5,5),0)
            invert_blur=255-blur_img
            pencil_sketch = cv2.divide(gray_img,invert_blur, scale=200.0)
            return pencil_sketch
    pass

############################################################### Scanning Class ###############################################################

class Scanning:

    #----------Scanning the Document----------
    def WrapPerspective_FUNC(img,width,height,p1,p2,p3,p4,effno=0,g=0.5,sharp=4,contras=2,threshs=17,bluring=3,bright_NO=50):
        width=width
        height=height
        pt1=np.float32([p1,p2,p3,p4])
        pt2=np.float32([[0,0],[width,0],[width,height],[0,height]])
        perspect=cv2.getPerspectiveTransform(pt1,pt2)
        wraped_img=cv2.warpPerspective(img,perspect,(int(width),int(height)))
        effects=Process.Image_Effect_FUNC(wraped_img,effno,g,sharpen=sharp,contracts=contras,thresh_C=threshs,blur_n=bluring,brights=bright_NO)
        imgp=Image.fromarray(effects).convert("RGB")
        imgp=imgp.resize((width,height),Image.LANCZOS)
        effects=np.array(imgp)
        return effects
    pass

############################################################### OCR Class ###############################################################

class OCR:

    #----------OCR Image to String----------
    def OCR_PROCESS_FUNC(img,ocr_path):
        ocr_location = ocr_path
        if(os.path.isfile(ocr_location)):
            pytesseract.pytesseract.tesseract_cmd=ocr_location
            return pytesseract.image_to_string(img,lang="eng"),pytesseract.image_to_boxes(img,lang="eng",config='--oem 3')
        else:
            msgbox.showerror("Error","Unable to find the Tesseract")
    pass

############################################################### EXPORT Class ###############################################################

class EXPORT:

    #----------Export of the PDF File----------
    def Export_PDF_FUNC(l1,data_file,dbtable,backup_folder,backuppaths,dos=True):
        resol = 200
        # qual = 130
        if len(l1)==0:
            msgbox.showerror("Error","Please ADD Image")
        elif len(l1)==1:
            files=filedialog.asksaveasfilename(defaultextension=".pdf")
            if files!="":
                os.chdir(os.path.dirname(files))
                ImageOps.expand(l1[0],border=1,fill="black").save(f"{os.path.basename(files)}","PDF",resolution=resol,jfif_unit=1, dpi=(72,72), jfif_density=(72,72))
                if dos==True:
                    os.chdir(os.path.dirname(data_file))

                    if os.path.isdir(backup_folder):
                        os.chdir(backup_folder)
                        ImageOps.expand(l1[0],border=1,fill="black").save(f"{os.path.basename(files)}","PDF",resolution=resol,jfif_unit=1, dpi=(72,72), jfif_density=(72,72))
                    else:
                        os.mkdir(backup_folder)
                        os.chdir(backup_folder)
                        ImageOps.expand(l1[0],border=1,fill="black").save(f"{os.path.basename(files)}","PDF",resolution=resol,jfif_unit=1, dpi=(72,72), jfif_density=(72,72))
                    DATABASE.Insert_DATABASE(data_file,f"{files}",dbtable,backuppaths)
                msgbox.showinfo("Successfull",f"The {files} has been Saved!")
                pass
        else:
            files=filedialog.asksaveasfilename(defaultextension=".pdf")
            if files!="":
                os.chdir(os.path.dirname(files))
                l1[0].save(f"{os.path.basename(files)}","PDF",resolution=resol,save_all=True,append_images=l1[1:],jfif_unit=1, dpi=(72,72), jfif_density=(72,72))
                if dos==True:
                    os.chdir(os.path.dirname(data_file))

                    if os.path.isdir(backup_folder):
                        os.chdir(backup_folder)
                        l1[0].save(f"{os.path.basename(files)}","PDF",resolution=resol,save_all=True,append_images=l1[1:],jfif_unit=1, dpi=(72,72), jfif_density=(72,72))
                    else:
                        os.mkdir(backup_folder)
                        os.chdir(backup_folder)
                        l1[0].save(f"{os.path.basename(files)}","PDF",resolution=resol,save_all=True,append_images=l1[1:],jfif_unit=1, dpi=(72,72), jfif_density=(72,72))
                    DATABASE.Insert_DATABASE(data_file,f"{files}",dbtable,backuppaths)
                msgbox.showinfo("Successfull",f"The {files} has been Saved!")
                pass
        pass

    #----------Export of the Image----------
    def Export_IMAGE_FUNC(img,data_file,dbtable,backup_folder,backuppaths,dos=True):
        files=filedialog.asksaveasfilename(defaultextension=".jpg",filetypes=[("PNG","*.png"),("JPG","*.jpg"),("TIFF","*.tiff"),("Bitmap","*.bmp")])
        if files!="":
            os.chdir(os.path.dirname(files))
            cv2.imwrite(f"{os.path.basename(files)}",img)
            if dos==True:
                os.chdir(os.path.dirname(data_file))
                if os.path.isdir(backup_folder):
                    os.chdir(backup_folder)
                    cv2.imwrite(f"{os.path.basename(files)}",img)
                else:
                    os.mkdir(backup_folder)
                    os.chdir(backup_folder)
                    cv2.imwrite(f"{os.path.basename(files)}",img)
                DATABASE.Insert_DATABASE(data_file,f"{files}",dbtable,backuppaths)
            msgbox.showinfo("Successfull",f"The {os.path.basename(files)} has been Saved!")
        pass

    #----------Export of the Word Document----------
    def Export_WORD_FUNC(txt,data_file,dbtable,backup_folder,backuppaths,dos=True):
        if txt.strip()!="":
            files=filedialog.asksaveasfilename(defaultextension=".txt",filetypes=[("Text Document","*.txt"),("Word Document","*.docx")])
            if files!="":
                f=open(files,"w+")
                f.write(txt)
                f.close()
                if dos==True:
                    os.chdir(os.path.dirname(data_file))
                    if os.path.isdir(backup_folder):
                        f=open(os.path.join(os.path.dirname(data_file),backup_folder,f"{os.path.basename(files)}").replace("\\","/"),"w+")
                        f.write(txt)
                        f.close()
                    else:
                        os.mkdir(backup_folder)
                        f=open(os.path.join(os.path.dirname(data_file),backup_folder,f"{os.path.basename(files)}").replace("\\","/"),"w+")
                        f.write(txt)
                        f.close()
                    DATABASE.Insert_DATABASE(data_file,f"{files}",dbtable,backuppaths)
                msgbox.showinfo("Successfull",f"The {files} has been Saved!")
        pass

    #----------Export of the List Images----------
    def Export_ADDLIST_FUNC(l1,data_file,dbtable,backup_folder,backuppaths,dos=True):
        if len(l1)==0:
            msgbox.showwarning("Warning","Please ADD Image")
        else:
            files=filedialog.asksaveasfilename(defaultextension=".jpg",filetypes=[("JPEG","*.jpg"),("PNG","*.png"),("TIFF","*.tiff"),("Bitmap","*.bmp")])
            if files!="":
                for index,j in enumerate(l1):
                    os.chdir(os.path.dirname(files))
                    l1[index].save(f"{os.path.splitext(os.path.basename(files))[0]}-{index+1}{os.path.splitext(os.path.basename(files))[1]}",resolution=140,quality=100)
                if dos==True:
                    DATABASE.Insert_DATABASE(data_file,f"{os.path.join(os.path.dirname(files),os.path.splitext(os.path.basename(files))[0])}-{index}{os.path.splitext(os.path.basename(files))[1]}".replace("\\","/"),dbtable,backuppaths)
                    os.chdir(os.path.dirname(data_file))
                    if os.path.isdir(backup_folder):
                        os.chdir(backup_folder)
                        for index,j in enumerate(l1):
                            l1[index].save(f"{os.path.splitext(os.path.basename(files))[0]}-{index+1}{os.path.splitext(os.path.basename(files))[1]}",resolution=140,quality=100)
                    else:
                        os.mkdir(backup_folder)
                        os.chdir(backup_folder)
                        for index,j in enumerate(l1):
                            l1[index].save(f"{os.path.splitext(os.path.basename(files))[0]}-{index+1}{os.path.splitext(os.path.basename(files))[1]}",resolution=140,quality=100)
                msgbox.showinfo("Successfull",f"The {files} has been Saved!")
        pass
    pass

############################################################### DATABASE Class ###############################################################

class DATABASE:

    #----------Insert the records in the database----------
    def Insert_DATABASE(dbfile,files,TAB,backup_Paths):
        os.chdir(os.path.dirname(dbfile))
        conn=sqlite3.connect(os.path.basename(dbfile))

        query=f"""
        SELECT count(*) FROM sqlite_master WHERE type='table' AND name='{TAB}';
        """
        if conn.execute(query).fetchall()[0][0]==0:
            conn.execute(f"CREATE TABLE {TAB}(FILENAME VARCHAR(20),FILEURL VARCHAR(50),FILEFORMAT VARCHAR(20),TIME VARCHAR(20),backup VARCHAR(70))")
            x=datetime.datetime.now()
            dates=f"{x.strftime('%d')} {x.strftime('%B')} {x.strftime('%Y')}, {x.strftime('%X')} {x.strftime('%p')}"
            insert_query=f"""
            INSERT INTO {TAB} VALUES('{os.path.basename(files)}','{files}','{os.path.splitext(os.path.basename(files))[1]}','{dates}','{backup_Paths}')
            """
            conn.execute(insert_query)
            conn.commit()
            conn.close()
        else:
            x=datetime.datetime.now()
            dates=f"{x.strftime('%d')} {x.strftime('%B')} {x.strftime('%Y')}, {x.strftime('%X')} {x.strftime('%p')}"
            insert_query=f"""
            INSERT INTO {TAB} VALUES('{os.path.basename(files)}','{files}','{os.path.splitext(os.path.basename(files))[1]}','{dates}','{backup_Paths}')
            """
            conn.execute(insert_query)
            conn.commit()
            conn.close()
        pass
    pass

if __name__ == "__main__":
    App=User()
    App.User_Interface()