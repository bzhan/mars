import matplotlib
import matplotlib as plt
matplotlib.use("TkAgg")
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.figure import Figure

import tkinter as tk
from tkinter import ttk

def get_data_time(res, program_name):
    DataState = {}
    for t in res["time_series"][program_name]:
        state = t["state"]
        for var, val in state.items():
            if var not in DataState.keys():
                DataState[var] = ([], [])
            DataState[var][0].append(t['time'])
            DataState[var][1].append(val)
    return DataState

class Graphapp(tk.Tk):
    def __init__(self, res, *args, **kwargs):
        tk.Tk.__init__(self, *args, **kwargs)
        tk.Tk.wm_title(self, "Graph GUI")
        
        container = tk.Frame(self)
        container.pack(side="top", fill="both", expand = True)
        container.grid_rowconfigure(0, weight=1)
        container.grid_columnconfigure(0, weight=1)
        self.res = res
        self.frames = {}

        frame = PlotPage(container, self, self.res)
        self.frames[PlotPage] = frame
        frame.grid(row=0, column=0, sticky="nsew")
        
        self.show_frame(PlotPage)

    def show_frame(self, cont):
        frame = self.frames[cont]
        frame.tkraise()


class PlotPage(tk.Frame):
    def __init__(self, parent, controller, res):
        tk.Frame.__init__(self, parent)

        self.res = res

        label1 = tk.Label(self, text="Program")
        label1.pack()

        self.program_name = tk.StringVar()
        self.e1 = ttk.Combobox(self, textvariable=self.program_name)
        self.e1.pack()
        self.e1.bind('<<ComboboxSelected>>', self.plot_graph)
        self.e1.state(["readonly"])

        self.program_names = tuple(sorted(self.res['time_series'].keys()))
        self.e1['values'] = self.program_names
        self.program_name.set(self.program_names[0])

        f = Figure(figsize=(5,5), dpi=100)
        self.a = f.add_subplot(111)

        self.canvas = FigureCanvasTkAgg(f, self)
        self.canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

        self.toolbar = NavigationToolbar2Tk(self.canvas, self)
        self.canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        self.plot_graph()

    def plot_graph(self, *args):
        if self.program_name.get() in self.program_names:
            self.a.clear()
            dataset_state = get_data_time(self.res, self.program_name.get())
            for t, (x, y) in dataset_state.items():
                self.a.plot(x, y, label=t)
                self.a.legend()
            self.canvas.draw()
            self.toolbar.update()
            self.e1.selection_clear()


def graph(res, proc_name=None, separate=False):
    app = Graphapp(res)
    app.mainloop()
