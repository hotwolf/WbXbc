###############################################################################
# WbXbc - Manual - Makefile                                                   #
###############################################################################
#    Copyright 2018 Dirk Heisswolf                                            #
#    This file is part of the WbXbc project.                                  #
#                                                                             #
#    WbXbc is free software: you can redistribute it and/or modify            #
#    it under the terms of the GNU General Public License as published by     #
#    the Free Software Foundation, either version 3 of the License, or        #
#    (at your option) any later version.                                      #
#                                                                             #
#    WbXbc is distributed in the hope that it will be useful,                 #
#    but WITHOUT ANY WARRANTY; without even the implied warranty of           #
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            #
#    GNU General Public License for more details.                             #
#                                                                             #
#    You should have received a copy of the GNU General Public License        #
#    along with WbXbc.  If not, see <http://www.gnu.org/licenses/>.           #
###############################################################################
# Version History:                                                            #
#   August 6, 2018                                                            #
#      - Initial release                                                      #
###############################################################################

#Source files
SRC_MAIN = WbXbc_manual.adoc

#ASCIIDoc command line arguments
HTML_ARGS   = -b html5 -a toc2
PDF_ARGS    = -r asciidoctor-pdf -b pdf
EPUB_ARGS   = -r asciidoctor-epub3 -b epub3
COMMON_ARGS = -r asciidoctor-bibtex -a toc -a imagesdir=img -D ..
#COMMON_ARGS = -r asciidoctor-diagram -a toc -a imagesdir=img -D ..

#By default build everything 
all: clean html pdf epub

#Set keywords
.PHONY: all html pdf epub clean

#HTML documentation
html:	*.adoc
	asciidoctor $(HTML_ARGS) $(COMMON_ARGS) $(SRC_MAIN)

#PDF documentation
pdf:    *.adoc
	asciidoctor $(PDF_ARGS) $(COMMON_ARGS) $(SRC_MAIN)

#EPUB documentation
epub:    *.adoc
	asciidoctor $(EPUB_ARGS) $(COMMON_ARGS) $(SRC_MAIN)
#Clean up
clean:
	rm -f ../*.html ../*.pdf ../*.epub



