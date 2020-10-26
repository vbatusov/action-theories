# Based on <https://www.youtube.com/watch?v=p_di4Zn4wz4>

import numpy as np
import drawSvg as draw
import random


# METAPARAMETERS
# Simulation step
dt = 0.01
# Total time
T = 3

class BoundingBox(object):
    def __init__(self, bb=None):
        self.bb = bb

    def add_pt(self, pt): # pt is a tuple of integers
        if not self.bb:
            self.bb = (pt, pt)
        else:
            self.bb = ((min(self.bb[0][0], pt[0]), min(self.bb[0][1], pt[1])), (max(self.bb[1][0], pt[0]), max(self.bb[1][1], pt[1])))

    def join(self, box):
        print("Joining", self.bb, "with", box.bb)
        if not self.bb:
            self.bb = box.bb
        else:
            pt1, pt2 = box.bb
            self.add_pt(pt1)
            self.add_pt(pt2)
        print("yielding", self.bb)

    def dimensions(self): # a tuple (width, height)
        if not self.bb:
            return None
        return (int(self.bb[1][0] - self.bb[0][0]), int(self.bb[1][1] - self.bb[0][1]))

class Curve(object):
    """ Just a list of tuples of numbers """
    def __init__(self, ivp, t):
        self.data = [pt for pt in ivp.curve(t)]
        self.originator = ivp

        # Bounding box
        self.box = BoundingBox()
        for pt in self.data:
            self.box.add_pt(pt)


class IVP(object):
    """ A curve is an initial value problem
        together with a generator """

    def __init__(self, name="Unknown", HARE=1000, WOLF=50):
        self.name = name
        # Constants
        self.alpha = 1.0     # Hare birthrate
        self.beta = 0.01     # Hare death by wolf
        self.delta = 0.003   # Wolf birthrate by hare
        self.gamma = 1.6    # Wolf natural die-off

        # Initial conditions
        self.HARE_0 = HARE
        self.WOLF_0 = WOLF

    # DE
    def dH(self, h, w):
        return h * (self.alpha - self.beta * w)

    def dW(self, h, w):
        return w * (self.delta * h - self.gamma)

    # Compute an entire curve from 0 to t
    # Exactly the same but generator
    def curve(self, t):
        # Init
        h = self.HARE_0
        w = self.WOLF_0

        yield (h, w)

        for time in np.arange(0, t, dt):
            # Direction vector
            dh = self.dH(h, w)
            dw = self.dW(h, w)

            # Take a step
            h += dh * dt
            w += dw * dt

            # Return the state at t
            yield (h, w)


class Canvas(object):
    def __init__(self, width, height):
        self.margin = 50
        self.width = width  #drawing area
        self.height = height
        self.xsize, self.ysize = width + 2*self.margin, height + 2*self.margin  # dimensions of entire canvas
        self.xo, self.yo = -(self.xsize )/2 + self.margin , -(self.ysize)/2 + self.margin       # offsets
        self.xsc, self.ysc = 1, 1 #0.3, 0.7                  # scaling
        self.d = draw.Drawing(self.xsize, self.ysize, origin="center")
        self.d.setPixelScale(2) # Set number of pixels per geometry unit
        self.outfile = "zayats.svg"

        self.prepare()

    def prepare(self):
        self.d.append(draw.Rectangle(self.xo - self.margin, self.yo - self.margin, self.xsize, self.ysize, fill="white"))
        #self.d.append(draw.Circle(0,0, 3, fill='orange'))
        #self.d.append(draw.Circle(10,0, 1, fill='orange'))
        #self.d.append(draw.Circle(0,10, 1, fill='orange'))
        self.draw_axes()

    def draw_axes(self):
        self.line((0, 0), (self.width, 0), w=3, col="red")
        self.line((0, 0), (0, self.height), w=3, col="red")
        #self.line((self.width, 0), (self.width, self.height), w=3, col="gray")
        #self.line((0, self.height), (self.width, self.height), w=3, col="gray")

        for x in range(0, self.width, 50):
            self.line((x, 0), (x, -7), w=1, col="red")
            self.text(str(x), 7, x, -5)

        for y in range(0, self.height, 50):
            self.line((0, y), (-7, y), w=1, col="red")
            self.text(str(y), 7, -5, y)

    def render(self):
        self.d.saveSvg(self.outfile)
        print("File {} saved.".format(self.outfile))

    def draw_curve(self, curve):
        # Draw starting point

        # Draw curve
        prev = None
        for (h,w) in curve.data:
            if not prev:
                prev = (h,w)

            # curve itself
            self.d.append(draw.Line(prev[0] * self.xsc + self.xo, prev[1] * self.ysc + self.yo, h * self.xsc + self.xo, w * self.ysc + self.yo, fill="none", stroke_width=0.3, stroke="black"))

            prev = (h,w)


        # endpoints and stuff
        self.d.append(draw.Circle(curve.data[0][0] * self.xsc + self.xo, curve.data[0][1] * self.ysc + self.yo, 2, fill='green'))
        self.d.append(draw.Circle(curve.data[-1][0] * self.xsc + self.xo, curve.data[-1][1] * self.ysc + self.yo, 2, fill='red'))
        self.text(curve.originator.name, 7, curve.data[0][0], curve.data[0][1])

        # Bounding box
        #self.rect(curve.box.bb[0][0], curve.box.bb[0][1], curve.box.dimensions()[0], curve.box.dimensions()[1])

    def line(self, c1, c2, w=1, col="#5555ff"):
        x1,y1 = c1
        x2,y2 = c2
        self.d.append(draw.Line(x1 * self.xsc + self.xo, y1* self.ysc + self.yo, x2* self.xsc + self.xo, y2* self.ysc + self.yo, fill="none", stroke_width=w, stroke=col))

    def circ(self, c, r, col="black"):
        self.d.append(draw.Circle(c[0] * self.xsc + self.xo, c[1] * self.ysc + self.yo, r, fill=col))

    def rect(self, x, y, w, h, col="black"):
        self.d.append(draw.Rectangle(x * self.xsc + self.xo, y * self.ysc + self.yo, w * self.xsc , h * self.ysc, fill="none", stroke_width=0.5, stroke=col))

    def text(self, text, size, x, y, center=2):
        self.d.append(draw.Text(text, size, x * self.xsc + self.xo, y * self.ysc + self.yo, center=center, fill='black'))





# Building curves
curves = []
curves.append(Curve(IVP(name="start"), random.randint(1, T)))
curves.append(Curve(IVP(name="remove hares", HARE=curves[0].data[-1][0] - 200, WOLF=curves[0].data[-1][1]), random.randint(1, T)))
curves.append(Curve(IVP(name="double wolves", HARE=curves[1].data[-1][0], WOLF=2*curves[1].data[-1][1]), random.randint(1, T)))
curves.append(Curve(IVP(name="stealthy hares", HARE=curves[2].data[-1][0], WOLF=curves[2].data[-1][1]), random.randint(1, T)))

common_box = BoundingBox()
common_box.add_pt((0,0))
for curve in curves:
    common_box.join(curve.box)
#ivps[3].beta /= 2
print(common_box.dimensions())

# field

l = .1

# Drawing
w, h = common_box.dimensions()
c = Canvas(w, h)

last_pt = None
for curve in curves:
    c.draw_curve(curve)
    if last_pt:
        c.line(last_pt, curve.data[0])
    last_pt = curve.data[-1]

#(c.xsize, c.ysize) = ivps[0].box.dimensions()
#print("Bounding box:", ivps[0].box.dimensions())

num_points = 1000
for p in range(0, num_points):
    x = random.randint(0, c.width)
    y = random.randint(0, c.height)
    c.circ((x, y), 0.5, col="cyan")
    c.line((x, y), (x + curves[0].originator.dH(x, y) * l, y + curves[0].originator.dW(x, y) * l), w=0.2, col="cyan")



c.render()
