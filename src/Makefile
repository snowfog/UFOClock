#
# Assumes you have installed freeglut3-dev and you have
# NOVAS C3.1 in your home directory.
#


UFOClock: sundial2.c moondata.c zipdata.c
	gcc -I ~/novas/Cdist -o $@ $^ ~/novas/Cdist/libnovas.a -lm -lGL -l GLU -lglut


#
# NOVAS was built like this:
#
# libnovas.a: novas.o novascon.o nutation.o solsys3.o readeph0.o
# 	ar ru $@ $^
# 	ranlib $@
