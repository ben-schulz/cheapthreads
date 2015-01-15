# Generic makefile for processing Beamer files
# 
# Rouben Rostamian <rostamian@umbc.edu>
# December 2004

BASE	= hfc

FIGURES = \
	p1p2.pdf \
	bedsupport1.pdf \
	bedsupport2.pdf \
	bedsupport3.pdf \
	bounce.pdf \
	cell-contours.pdf \
	cell-lines.pdf \
	cell-mesh.pdf \
	cell-shaded.pdf \
	efficiency.pdf \
	lambertW.pdf \
	pde1.pdf \
	pde2.pdf \
	pressure.pdf \
	schematic1.pdf \
	schematic2.pdf \
	tube.pdf \
	fcc.jpg \

$(BASE).pdf: $(BASE).tex $(FIGURES)
	@(\
	AUX=$(BASE).aux; \
	if [ ! -f $$AUX ]; then pdflatex $(BASE); fi; \
	pages1=`sed -n '/inserttotalframenumber/{ s/[^0-9]//g; p; }' < $$AUX`; \
	pdflatex $(BASE); \
	pages2=`sed -n '/inserttotalframenumber/{ s/[^0-9]//g; p; }' < $$AUX`; \
	if [ $$pages1 -ne $$pages2 ]; then pdflatex $(BASE); fi; \
	)
	

.PHONY: clean

clean:
	@rm -f $(BASE).{aux,log,nav,out,pdf,snm,toc}
