# Will need to install:
#
#   1. PyPNG package
#   2. pngcrush commandline tool

import json
import png
import numpy as np
import os

bits = 8


def read_mat(file_name):
    with open(file_name, "r") as f:
        values = json.loads(f.readline())
    M = np.array(values)
    return np.flipud(M)

def scale_it(val, v_min, v_mean, v_max, t_min, t_mean, t_max):
    # Scales value val piecewise linearly, so that
    #   0      -> 0
    #   v_min  -> t_min
    #   v_mean -> t_mean
    #   v_max  -> t_max
    if val == 0:
        return 0
    if val <= v_mean:
        m = (t_mean - t_min) / (v_mean - v_min)
        b = t_min - m * v_min
    if val > v_mean:
        m = (t_max - t_mean) / (v_max - v_mean)
        b = t_max - m * v_max
    return round(m * val + b)

def adjust_mat(M, bits):
    # Adjusts the values in M appropriately, to use bits bits.
    rooter = lambda x: x ** (1/3)
    Mroot = np.array([rooter(x) for x in M])
    # We only care about the nonzero values in Mroot.
    Vals = Mroot.flatten()
    Vals = Vals[Vals > 0]
    # What does our data look like?
    v_min = Vals.min()
    v_max = Vals.max()
    v_mean = Vals.mean()
    # What are we going to scale to?
    t_min = 1
    t_max = 2**bits - 1
    #t_mean = round( t_max * v_mean / v_max )
    t_mean = 64
    # Now do the scaling.
    # Doing it the stupid way because don't want to figure out vectorization.
    Madj = np.zeros([len(M), len(M[0])])
    for i in range(len(M)):
        for j in range(len(M[0])):
            Madj[i,j] = scale_it(Mroot[i,j], v_min, v_mean, v_max, t_min, t_mean, t_max)
    return t_max - Madj

def jay_adjust_mat(M, bits):
    # Adjusts the values in M appropriately, to use bits bits.
    rooter = lambda x: x ** (1/2)
    Mroot = np.array([rooter(x) for x in M])
    max_val = max(map(max,Mroot))

    # # We only care about the nonzero values in Mroot.
    # Vals = Mroot.flatten()
    # Vals = Vals[Vals > 0]
    # # What does our data look like?
    # v_min = Vals.min()
    # v_max = Vals.max()
    # v_mean = Vals.mean()
    # # What are we going to scale to?
    # t_min = 1
    t_max = 2**bits - 1
    # #t_mean = round( t_max * v_mean / v_max )
    # t_mean = 64
    # # Now do the scaling.
    # # Doing it the stupid way because don't want to figure out vectorization.
    # Madj = np.zeros([len(M), len(M[0])])
    # for i in range(len(M)):
    #     for j in range(len(M[0])):
    #         Madj[i,j] = scale_it(Mroot[i,j], v_min, v_mean, v_max, t_min, t_mean, t_max)
    return t_max * (1 - Mroot / max_val)
    # return t_max - Madj
    
def write_png(file_name, M):
    M = M.astype(np.uint8) if bits == 8 else M.astype(np.uint8)
    with open(".temp.png", "wb") as f:
        w = png.Writer(len(M[0]), len(M), greyscale=True, bitdepth=bits)
        w.write(f, M)
        f.close()
        os.system(f"pngcrush -brute -newtimestamp .temp.png {file_name}")
        os.system("rm .temp.png")

def make_png(string):
    M = read_mat("samples/sample_len_300_1m_" + string + ".txt")
    M = jay_adjust_mat(M, bits)
    write_png("jay-pngs/" + string + ".png", M)

Filenames = ["0123", "0132", "0321",
             "0123_0132", "0123_0213", "0123_0231", "0123_0321", "0123_1032", "0123_1230",
             "0123_1302", "0123_1320", "0123_2301", "0123_2310", "0123_3120", "0132_0213",
             "0132_0231", "0132_0321", "0132_1023", "0132_1032", "0132_1203", "0132_1230",
             "0132_1302", "0132_1320", "0132_2103", "0132_2130", "0132_2301", "0132_2310",
             "0132_3120", "0213_0231", "0213_0321", "0213_1032", "0213_1230", "0213_1302",
             "0213_1320", "0213_2301", "0213_3120", "0231_0312", "0231_0321", "0231_1032",
             "0231_1203", "0231_1230", "0231_1302", "0231_1320", "0231_2013", "0231_2031",
             "0231_2103", "0231_2130", "0231_2301", "0231_3012", "0231_3102", "0321_1032",
             "0321_1230", "0321_1302", "0321_2103", "0321_2301", "1032_1302", "1032_2301",
             "1302_2031",
             "1-box-2-box-3",
             "0123_135024_145023_235014_245013_345012",
             "0132_0213_0321_23014",
             "0213_13042_20413_315042",
             "02143_02413_02431",
             "02314_03124_03214_13042_20413_315042",
             "domino",
             "juxta",
             "widdershins"]
just_weird = ["0123_3120"]

def do_all():
    for f in just_weird:
        print(f)
        make_png(f)

do_all()






