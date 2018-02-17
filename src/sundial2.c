/* Copyright (c) 2005, Matt Wronkiewicz
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without modification, are
 * permitted provided that the following conditions are met:
 * 
 * Redistributions of source code must retain the above copyright notice, this list of
 * conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright notice, this list
 * of conditions and the following disclaimer in the documentation and/or other materials
 * provided with the distribution.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT
 * SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
 * WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. */

/* Parts of this file are based on Sundial, by George Williams. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include "novas.h"
#include "moondata.h"
#include "zipdata.h"

static body earth;
static body sun;
static body moon;
static site_info geo_loc = {34.0, -119.0, 34, 0.0, 0.0};

static time_t sunrise, sunset, noon, midnight;
static time_t twilight_morn, twilight_eve;
static time_t twilightn_morn, twilightn_eve;
static time_t twilighta_morn, twilighta_eve;
static double moonpos;
static double yearpos;
static int test_off = 0;
/* sunrise has the zenith distance at 90.8333, moonrise (more approximately) 90.5666 */
/* sunset has the zenith distance again at 90.8333 */
/* noon has the azimuth at 180 */
/* midnight has the azimuth at 0 */
	/* I hope */
/* civil twilight has zenith distance at 96 */
/* nautical twilight has zenith distance at 102 */
/* astronomical twilight has zenith distance at 108 */

static time_t jul2time(double jul) {
    static float base=0;

    if ( base==0 )
	base = julian_date(1970, 1, 1, 0);
    jul -= base;
    jul *= 24*60*60.0;
return( jul );
}

static double interpolate_linear(const double xa, const double ya,
	const double xb, const double yb, const double x) {
    const double interval = xb - xa;
    const double dx = (interval == 0)?0:(x - xa)/interval;
    return ya + (yb - ya)*dx;
}

static double findnoonmid(float seek,double az[29],double appnoon) {
    double top, bottom, mid = 0;
    double right_ascension, declination, distance_to_earth;
    double rar, decr, zd, azimuth;
    int i;

    if ( seek==0 ) {
	for ( i=1; i<=29; ++i )
	    if ( az[i-1]>300 && az[i]<=60 )
	break;
    } else {
	for ( i=1; i<=29; ++i )
	    if ( az[i-1]<seek && az[i]>=seek )
	break;
    }
    top = appnoon + (i-14)/24.0;
    bottom = appnoon + (i-15)/24.0;
    while ( top-bottom > 1/(24*60*30.0) ) {
	mid = (top+bottom)/2;
	topo_planet(mid, &sun, &earth, 0, &geo_loc,
		&right_ascension, &declination, &distance_to_earth);
	equ2hor(mid, 0, 0,0, &geo_loc,
		right_ascension, declination, 1,
		&zd, &azimuth, &rar, &decr);
	if ( azimuth==seek )
	    return( mid );
	if ( seek==0 ) {
	    if ( azimuth < 20 )
		top = mid;
	    else
		bottom = mid;
	} else {
	    if ( azimuth>180 )
		top = mid;
	    else
		bottom = mid;
	}
    }
    return( mid );
}

static double findsunriseset(const int start, const double zd[29],
	const double appnoon, const double goal) {
    double top;
    double bottom;
    double mid = 0;
    int i = start;

    for (; i <= 29; i++) {
	if (start < 6 && zd[i-1] >= goal && zd[i] < goal)
	    break;
	else if (start >= 6 && zd[i-1] <= goal && zd[i] > goal)
	    break;
    }
    top = appnoon + (i - 14)/24.0;
    bottom = appnoon + (i - 15)/24.0;
    while (top - bottom > 1/(24*60*30.0)) {
	double zenith;
	mid = (top + bottom)/2;
	{
	    double right_ascension;
	    double declination;
	    double distance_to_earth;
	    double rar;
	    double decr;
	    double az;
	    topo_planet(mid, &sun, &earth, 0, &geo_loc, &right_ascension,
		    &declination, &distance_to_earth);
	    equ2hor(mid, 0, 0, 0, &geo_loc, right_ascension, declination, 1,
		    &zenith, &az, &rar, &decr);
	}
	if (zenith == goal)
	    return mid;
	if ((start < 6 && zenith < goal) || (start >= 6 && zenith > goal))
	    top = mid;
	else
	    bottom = mid;
    }
    return mid;
}

static const double PI = 3.1415927;

static double moon_position(const double j) {
    static double last_new_j = 0;
    static double next_new_j = 0;
    static double last_phase = 0;
    if (j < last_new_j || j > next_new_j) {
	int i = 0;
	for (; i < 1237; i++) {
	    const double jd = phases[i].jd;
	    if (jd < j) {
		last_new_j = jd;
		last_phase = phases[i].phase;
	    }
	    else {
		next_new_j = jd;
		break;
	    }
	}
    }
    return interpolate_linear(last_new_j, last_phase,
	    next_new_j, last_phase + 0.25, j)*360;
}

static void findtimes(time_t approximate_noon, time_t now) {
    double zd[29], az[29];
    /* lat, lon, altitude, temperature (Celcius), pressure (millibars) */
    double right_ascension, declination, distance_to_earth;
    double rar, decr;
    struct tm *tm;
    double tjd;
    double startjd;
    int i;
    int error;
    double dsunrise, dsunset, dnoon, dmidnight, dtwim, dtwie;

    if (error = set_body (0,3,"Earth", &earth)) {
	fprintf (stderr,"Error %d from set_body.\n", error);
	exit (1);
    }
    if (error = set_body (0,10,"Sun", &sun)) {
	fprintf (stderr,"Error %d from set_body.\n", error);
	exit (1);
    }
    if (error = set_body (0,11,"Moon", &moon)) {
	fprintf (stderr,"Error %d from set_body.\n", error);
	exit (1);
    }

    tm = gmtime(&approximate_noon);
    startjd = julian_date(tm->tm_year+1900, tm->tm_mon+1, tm->tm_mday, tm->tm_hour);
    for ( i= -14; i<=14; ++i ) {
	tjd = julian_date(tm->tm_year+1900, tm->tm_mon+1, tm->tm_mday, tm->tm_hour+i);
	topo_planet(tjd, &sun, &earth, 0, &geo_loc,
		&right_ascension, &declination, &distance_to_earth);
	/*if (i == 0)
		printf("Right ascension %f\n", (float)right_ascension);*/
	equ2hor(tjd, 0, 0,0, &geo_loc,
		right_ascension, declination, 1,
		&zd[i+14], &az[i+14], &rar, &decr);
    }

    dnoon = findnoonmid(180.0,az,startjd);
    noon = jul2time(dnoon);
    dmidnight = findnoonmid(0.0,az,startjd);
    midnight = jul2time(dmidnight);

    dsunrise = findsunriseset(2,zd,startjd,90.2667);
    dsunset = findsunriseset(14,zd,startjd,90.2667);
    sunrise = jul2time(dsunrise);
    sunset = jul2time(dsunset);

    dtwim = findsunriseset(2,zd,startjd,96);
    dtwie = findsunriseset(14,zd,startjd,96);
    twilight_morn = jul2time(dtwim);
    twilight_eve  = jul2time(dtwie);

    dtwim = findsunriseset(2,zd,startjd,102);
    dtwie = findsunriseset(14,zd,startjd,102);
    twilightn_morn = jul2time(dtwim);
    twilightn_eve  = jul2time(dtwie);

    dtwim = findsunriseset(2,zd,startjd,108);
    dtwie = findsunriseset(14,zd,startjd,108);
    twilighta_morn = jul2time(dtwim);
    twilighta_eve  = jul2time(dtwie);

    tm = gmtime(&now);
    startjd = julian_date(tm->tm_year+1900, tm->tm_mon+1, tm->tm_mday,
	    tm->tm_hour + tm->tm_min/60.0 + tm->tm_sec/60.0/60.0);
    moonpos = moon_position(startjd);
    
    topo_planet(startjd, &sun, &earth, 0, &geo_loc,
            &right_ascension, &declination, &distance_to_earth);
    yearpos = 90 - right_ascension*360/24;
}

static void findtoday(void) {
    time_t now;
    struct tm *tm;

    time(&now);
    now += test_off;
    tm = localtime(&now);
    findtimes( now-((tm->tm_hour*60L+tm->tm_min)*60L+tm->tm_sec) +12*60*60L, now);
}

#include <sys/types.h>
#include <sys/time.h>
#include <unistd.h>

#pragma ghs nowarning 494
#include <GL/glut.h>
#pragma ghs endnowarning

static int win;

static double deg2rad(const double deg) {
    return 2*PI*(90 - deg)/360;
}

static void drawArc(float start, float end, float inner, float outer, float stretchiw) {
    int i = 0;
    const int divs = (end - start)/6;
    glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
    glBegin(GL_TRIANGLES);
    for (; i < divs; i++) {
	const float a1 = deg2rad(start + i*(end - start)/divs);
	const float a2 = deg2rad(start + (i + 1)*(end - start)/divs);
	const float a1ix = cosf(a1)*inner*stretchiw;
	const float a1iy = sinf(a1)*inner;
	const float a1ox = cosf(a1)*outer;
	const float a1oy = sinf(a1)*outer;
	const float a2ix = cosf(a2)*inner*stretchiw;
	const float a2iy = sinf(a2)*inner;
	const float a2ox = cosf(a2)*outer;
	const float a2oy = sinf(a2)*outer;
	glVertex2f(a1ix, a1iy);
	glVertex2f(a1ox, a1oy);
	glVertex2f(a2ix, a2iy);
	glVertex2f(a2ix, a2iy);
	glVertex2f(a2ox, a2oy);
	glVertex2f(a1ox, a1oy);
    }
    glEnd();
}

static void drawTick(float angle, float radius, float length) {
    const float a = 2*PI*(90 - angle)/360;
    const float a1x = cosf(a)*(radius - length);
    const float a1y = sinf(a)*(radius - length);
    const float a2x = cosf(a)*radius;
    const float a2y = sinf(a)*radius;
	const float dx = a2x - a1x;
	const float dy = a2y - a1y;
    glBegin(GL_TRIANGLES);
    glVertex2f(a1x + 0.35*dy, a1y - 0.35*dx);
    glVertex2f(a1x - 0.35*dy, a1y + 0.35*dx);
    glVertex2f(a2x, a2y);
    glEnd();
}

static void drawHalfTickOpen(float angle, float radius, float length) {
    const float a = 2*PI*(90 - angle)/360;
    const float a1x = cosf(a)*(radius - length);
    const float a1y = sinf(a)*(radius - length);
    const float a2x = cosf(a)*radius;
    const float a2y = sinf(a)*radius;
	const float dx = a2x - a1x;
	const float dy = a2y - a1y;
    glBegin(GL_TRIANGLES);
    glVertex2f(a1x - 0.35*dy, a1y + 0.35*dx);
    glVertex2f(a1x, a1y);
    glVertex2f(a2x, a2y);
    glEnd();
}

static void drawHalfTickClose(float angle, float radius, float length) {
    const float a = 2*PI*(90 - angle)/360;
    const float a1x = cosf(a)*(radius - length);
    const float a1y = sinf(a)*(radius - length);
    const float a2x = cosf(a)*radius;
    const float a2y = sinf(a)*radius;
	const float dx = a2x - a1x;
	const float dy = a2y - a1y;
    glBegin(GL_TRIANGLES);
    glVertex2f(a1x, a1y);
    glVertex2f(a1x + 0.35*dy, a1y - 0.35*dx);
    glVertex2f(a2x, a2y);
    glEnd();
}

static void drawSun() {
    GLUquadricObj* const q = gluNewQuadric();
    glColor3b(127, 127, 127);
    gluDisk(q, 0.0, 0.1, 20, 2);
    glColor3b(0, 0, 0);
    gluDisk(q, 0.07, 0.1, 20, 2);
    gluDisk(q, 0.0, 0.02, 20, 2);
    gluDeleteQuadric(q);
}

static void drawMoon() {
    glColor3b(127, 127, 127);
    drawArc(0.0, 360.0, 0.0, 0.1, 1.0);
    glColor3b(0, 0, 0);
    drawArc(180.0, 360.0, 0.097, 0.1, 0.3);
}

static void drawEarth() {
    GLUquadricObj* const q = gluNewQuadric();
    glColor3b(127, 127, 127);
    gluDisk(q, 0.0, 0.12, 20, 2);
    glColor3b(0, 0, 0);
    gluDisk(q, 0.07, 0.1, 20, 2);
    glBegin(GL_TRIANGLES);
    glVertex2f(-0.015, 0.1);
    glVertex2f(0.015, 0.1);
    glVertex2f(0.015, -0.1);
    glVertex2f(-0.015, 0.1);
    glVertex2f(0.015, -0.1);
    glVertex2f(-0.015, -0.1);
    glVertex2f(-0.1, 0.015);
    glVertex2f(0.1, 0.015);
    glVertex2f(0.1, -0.015);
    glVertex2f(-0.1, 0.015);
    glVertex2f(0.1, -0.015);
    glVertex2f(-0.1, -0.015);
    glEnd();
    gluDeleteQuadric(q);
}

static void disp(void) {
    float sun_angle;
    float horiz_angle;
    float rise_angle;
    float set_angle;
    const time_t now = time(NULL) + test_off;
	float midnight_angle = (noon < midnight)?180:-180;
    int i = 0;
    findtoday();
    sun_angle = interpolate_linear(noon, 0, midnight, midnight_angle, now);
    rise_angle = interpolate_linear(noon, 0, midnight, midnight_angle, sunrise);
    set_angle = interpolate_linear(noon, 0, midnight, midnight_angle, sunset);
    horiz_angle = interpolate_linear(rise_angle, abs(rise_angle), set_angle, abs(set_angle), sun_angle);
    glPushMatrix();
    {
	const float width = glutGet(GLUT_WINDOW_WIDTH);
	const float height = glutGet(GLUT_WINDOW_HEIGHT);
	if (width > height)
	    gluOrtho2D(-width/height, width/height, -1.0, 1.0);
	else
	    gluOrtho2D(-1.0, 1.0, -height/width, height/width);
    }
    glClear(GL_COLOR_BUFFER_BIT);
    glColor3b(0, 0, 0);
    glMatrixMode(GL_MODELVIEW);

    drawArc(horiz_angle - sun_angle, 360 - horiz_angle - sun_angle, 0.0, 0.8, 1.0);
    drawTick(-sun_angle, 0.8, 0.15);
    
    drawArc(0, 360, 0.45, 0.55, 1.0);
    glColor3b(127, 127, 127);
    drawArc(horiz_angle - sun_angle, 360 - horiz_angle - sun_angle, 0.45, 0.55, 1.0);
    glColor3b(0, 0, 0);
    for (; i < 4; i++) {
        const float degs = i*90;
        drawTick(degs, 0.45, 0.15);
    }
    glColor3b(127, 127, 127);
    for (; i < 9; i++) {
        const float degs = i*90 - 360;
        if (horiz_angle - sun_angle < degs && 360 - horiz_angle - sun_angle > degs)
            drawTick(degs, 0.45, 0.15);
    }
    glPushMatrix();
    glTranslatef(cosf(deg2rad(yearpos))*0.5,
	    sinf(deg2rad(yearpos))*0.5, 0.0);
    drawEarth();
    glPopMatrix();

    glPushMatrix();
    glTranslatef(cosf(deg2rad(-moonpos))*0.9,
	    sinf(deg2rad(-moonpos))*0.9, 0.0);
    drawMoon();
    glPopMatrix();

    glPushMatrix();
    glTranslatef(0.0, 0.9, 0.0);
    drawSun();
    glPopMatrix();

    glColor3b(127, 127, 127);
    drawHalfTickClose(
	    interpolate_linear(noon, 0, midnight, midnight_angle, twilight_eve) - sun_angle,
	    0.8, 0.15);
    drawHalfTickClose(
	    interpolate_linear(noon, 0, midnight, midnight_angle, twilightn_eve) - sun_angle,
	    0.8, 0.15);
    drawHalfTickClose(
	    interpolate_linear(noon, 0, midnight, midnight_angle, twilighta_eve) - sun_angle,
	    0.8, 0.15);
    drawHalfTickOpen(
	    interpolate_linear(noon, 0, midnight, midnight_angle, twilight_morn) - sun_angle,
	    0.8, 0.15);
    drawHalfTickOpen(
	    interpolate_linear(noon, 0, midnight, midnight_angle, twilightn_morn) - sun_angle,
	    0.8, 0.15);
    drawHalfTickOpen(
	    interpolate_linear(noon, 0, midnight, midnight_angle, twilighta_morn) - sun_angle,
	    0.8, 0.15);
    drawTick(midnight_angle - sun_angle, 0.8, 0.15);
    glPopMatrix();
    glutSwapBuffers();
}

static int test_mode = 0;
static int test_accel = 0;

static void timer(int t) {
    if (test_mode)
	test_off += test_accel;
    disp();
    glutTimerFunc(test_mode?50:5000, timer, t);
}

static void keyb(unsigned char key, int x, int y) {
    if (key == 'q') {
	glutDestroyWindow(win);
	exit(0);
    }
    else if (key == 't') {
	test_mode = 1;
	test_accel += 300;
	glutTimerFunc(50, timer, 0);
    }
    else if (key == 'n') {
	test_mode = 0;
	test_accel = 0;
	test_off = 0;
    }
}

void reshape(int width, int height) {
    glViewport(0, 0, width, height);
}

#include <sys/param.h>

int main(int argc, char **argv) {
    int i;
    char* homedir = NULL;
    char configpath[MAXPATHLEN];
    FILE* cfgfile = NULL;

    glutInit(&argc, argv);
    
    homedir = getenv("HOME");
    strcpy(configpath, homedir);
    strcat(configpath, "/.UFOClock");
    cfgfile = fopen(configpath, "r");
    if (cfgfile != NULL) {
        int latitude_set = 0;
        int longitude_set = 0;
        while (1) {
            char buf[128];
            const char* const ret = fgets(buf, 128, cfgfile);
            char* const endlpos = strchr(buf, '\n');
            if (ret == NULL)
                break;
            if (buf[0] == '\n' || buf[0] == '\0' || buf[0] == '#')
                continue;
            if (endlpos != NULL)
                endlpos[0] = '\0';
            if (strncmp(buf, "latitude=", strlen("latitude=")) == 0) {
                geo_loc.latitude = strtod(&buf[strlen("latitude=")], NULL);
                latitude_set = 1;
            }
            else if (strncmp(buf, "lat=", strlen("lat=")) == 0) {
                geo_loc.latitude = strtod(&buf[strlen("lat=")], NULL);
                latitude_set = 1;
            }
            else if (strncmp(buf, "longitude=", strlen("longitude=")) == 0) {
                geo_loc.longitude = strtod(&buf[strlen("longitude=")], NULL);
                longitude_set = 1;
            }
            else if (strncmp(buf, "long=", strlen("long=")) == 0) {
                geo_loc.longitude = strtod(&buf[strlen("long=")], NULL);
                longitude_set = 1;
            }
            else if (strncmp(buf, "height=", strlen("height=")) == 0) {
                geo_loc.height = strtod(&buf[strlen("height=")], NULL);
            }
            else if (strncmp(buf, "zip=", strlen("zip=")) == 0) {
                const int zip = strtol(&buf[strlen("zip=")], NULL, 10);
                int ze = 0;
                for (; ze < sizeof(zip_codes)/sizeof(struct zip_info); ze++) {
                    if (zip_codes[ze].zip != zip)
                        continue;
                    if (!latitude_set)
                        geo_loc.latitude = zip_codes[ze].latitude;
                    if (!longitude_set)
                        geo_loc.longitude = zip_codes[ze].longitude;
                }
            }
            else {
                printf("Error: Unhandled line:\n%s\n", buf);
                exit(1);
            }
        }
        fclose(cfgfile);
    }

    for ( i=1; i<argc; ++i ) {
	if ( strcmp("-lat",argv[i])==0 || strcmp("-latitude",argv[i])==0 )
	    geo_loc.latitude = strtod(argv[++i],NULL);
	else if ( strcmp("-lon",argv[i])==0 || strcmp("-longitude",argv[i])==0 )
	    geo_loc.longitude = strtod(argv[++i],NULL);
	else {
	    fprintf(stderr,"Usage: %s [-lat num] [-lon num]\n", argv[0] );
	    exit(1);
	}
    }
    glutInitWindowSize(96, 96);
    glutInitDisplayMode(GLUT_RGB | GLUT_DOUBLE);
    win = glutCreateWindow("UFOClock");
    glutDisplayFunc(disp);
    glutKeyboardFunc(keyb);
    glutReshapeFunc(reshape);
    glutTimerFunc(5000, timer, 0);
    glClearColor(1.0,1.0,1.0,1.0);
    glutMainLoop();
    return 0;
}
