#!/bin/sh

for FILENAME in *.svg; do
    BASENAME="${FILENAME%.svg}";
    convert "${BASENAME}.svg" -transparent white "${BASENAME}.png";
done

for FILENAME in *.dia; do
    BASENAME="${FILENAME%.dia}";
    dia --export="${BASENAME}.pdf" "${BASENAME}.dia";
    pdfcrop "${BASENAME}.pdf";
    convert -density 144x144 "${BASENAME}-crop.pdf" -transparent white "${BASENAME}.png";
    rm "${BASENAME}.pdf" "${BASENAME}-crop.pdf"
done