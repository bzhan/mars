import matplotlib
matplotlib.use("TkAgg")
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.figure import Figure

import tkinter as tk
from tkinter import ttk

import numpy as np 

LARGE_FONT= ("Verdana", 12)

# Change the res dict here with what we got from exec_parallel
# function. 
res = { 
    'time_series': {
    'P1': 0,
    'P2': 1
    }
}

def get_program(res):
    return res.get('time_series').keys()

# def get_total_time(res):
#     return res.get('time') 

def get_data_time(res, ProgramName):
    temp_program_list = res.get('time_series').get(ProgramName)
    dataset_state = {}
    dataset_time = {}
    for new_entry in temp_program_list:
        for state_entry in new_entry.get('state'):
            for state_key in state_entry.keys():
                if not state_key in dataset_state:
                    dataset_state.update({state_key : []})
                    dataset_time.update({state_key : []})
                dataset_state.get(state_key).append(state_entry.get(state_key))
                dataset_time.get(state_key).append(new_entry.get('time'))
    return dataset_state, dataset_time




class Graphapp(tk.Tk):

    def __init__(self, *args, **kwargs):
        
        tk.Tk.__init__(self, *args, **kwargs)

        #tk.Tk.iconbitmap(self, default="clienticon.ico")
        tk.Tk.wm_title(self, "Graph GUI")
        
        
        container = tk.Frame(self)
        container.pack(side="top", fill="both", expand = True)
        container.grid_rowconfigure(0, weight=1)
        container.grid_columnconfigure(0, weight=1)

        self.frames = {}

        for F in (StartPage, PageOne, PageTwo, PageThree):

            frame = F(container, self)

            self.frames[F] = frame

            frame.grid(row=0, column=0, sticky="nsew")

        self.show_frame(StartPage)

    def show_frame(self, cont):

        frame = self.frames[cont]
        frame.tkraise()

        
class StartPage(tk.Frame):

    def __init__(self, parent, controller):
        tk.Frame.__init__(self,parent)
        label = tk.Label(self, text="Start Page", font=LARGE_FONT)
        label.pack(pady=10,padx=10)

        button1 = ttk.Button(self, text="Visit Graphing",
                            command=lambda: controller.show_frame(PageThree))
        button1.pack()

        button2 = ttk.Button(self, text="Quit",
                            command=lambda: quit)
        button2.pack()



class PageOne(tk.Frame):

    def __init__(self, parent, controller):
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="Page One!!!", font=LARGE_FONT)
        label.pack(pady=10,padx=10)

        button1 = ttk.Button(self, text="Back to Home",
                            command=lambda: controller.show_frame(StartPage))
        button1.pack()

        button2 = ttk.Button(self, text="Page Two",
                            command=lambda: controller.show_frame(PageTwo))
        button2.pack()


class PageTwo(tk.Frame):

    def __init__(self, parent, controller):
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="Page Two!!!", font=LARGE_FONT)
        label.pack(pady=10,padx=10)

        button1 = ttk.Button(self, text="Back to Home",
                            command=lambda: controller.show_frame(StartPage))
        button1.pack()

        button2 = ttk.Button(self, text="Page One",
                            command=lambda: controller.show_frame(PageOne))
        button2.pack()


class PageThree(tk.Frame):

    def __init__(self, parent, controller):
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="Graph Page!", font=LARGE_FONT)
        label.pack(pady=10,padx=10)

        button1 = ttk.Button(self, text="Back to Home",
                            command=lambda: controller.show_frame(StartPage))
        button1.pack()

        label1 = tk.Label(self, text="Program")
        label1.pack()
        e1 = tk.Entry(self, bd = 5)
        e1.pack()

        f = Figure(figsize=(5,5), dpi=100)
        a = f.add_subplot(111)
        

        def plot_graph():
            if (e1.get() in get_program(res)):
                # x = np.arange(0,4*np.pi,0.1)   # start,stop,step
                # y1 = np.sin(x)
                # y2 = np.cos(x)
                # a.plot(x,y1)
                # a.plot(x,y2) 
                dataset_state, dataset_time = get_data_time(res, e1.get())
                for t in dataset_state.keys():
                    x = dataset_state.get(t)
                    y = dataset_time.get(t)
                    a.plot(x,y,label = t)
                    a.legend()
                canvas = FigureCanvasTkAgg(f, self)
                canvas.draw()
                canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

                toolbar = NavigationToolbar2Tk(canvas, self)
                toolbar.update()
                canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)


        button2 = ttk.Button(self, text="Draw",
                            command=plot_graph)
        button2.pack()

        # canvas = FigureCanvasTkAgg(f, self)
        # canvas.draw()
        # canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

        # toolbar = NavigationToolbar2Tk(canvas, self)
        # toolbar.update()
        # canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        

    

app = Graphapp()
app.mainloop()