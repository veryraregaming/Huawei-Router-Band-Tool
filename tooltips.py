import tkinter as tk
from tkinter import ttk

class ToolTip:
    """
    Create a tooltip for a given widget
    """
    def __init__(self, widget, text, delay=500):
        self.widget = widget
        self.text = text
        self.delay = delay  # Reduced delay to 500ms (0.5 seconds)
        self.tip_window = None
        self.id = None
        
        widget.bind("<Enter>", self.schedule)
        widget.bind("<Leave>", self.cancel)
        widget.bind("<ButtonPress>", self.cancel)
    
    def schedule(self, event=None):
        self.cancel()
        self.id = self.widget.after(self.delay, self.show_tip)
    
    def cancel(self, event=None):
        if self.id:
            self.widget.after_cancel(self.id)
            self.id = None
        if self.tip_window:
            self.tip_window.destroy()
            self.tip_window = None
    
    def show_tip(self):
        if self.tip_window:
            return
        
        x = self.widget.winfo_rootx() + self.widget.winfo_width() // 2
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 5
        
        self.tip_window = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{x}+{y}")
        
        label = ttk.Label(tw, text=self.text, justify=tk.LEFT,
                          background="#FFFFCC", relief=tk.SOLID, borderwidth=1,
                          font=("Segoe UI", 9), padding=(5, 3),
                          wraplength=300)
        label.pack(padx=3, pady=3)

def create_tooltip(widget, text):
    """
    Create a tooltip for a given widget
    """
    return ToolTip(widget, text) 