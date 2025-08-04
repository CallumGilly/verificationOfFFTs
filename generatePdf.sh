agda --latex-dir=Thesis --latex Model.lagda
agda --latex-dir=Thesis --latex ProofWriteup.lagda

pdflatex thesis.tex
bibtex thesis
pdflatex thesis.tex
firefox thesis.pdf

texcount thesis.tex -inc -total
