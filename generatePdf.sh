agda --latex-dir=Thesis --latex Model.lagda
agda --latex-dir=Thesis --latex ProofWriteup.lagda
agda --latex-dir=Thesis --latex Implementation.lagda

pdflatex thesis.tex
bibtex thesis
pdflatex thesis.tex
firefox thesis.pdf

texcount thesis.tex -inc -total
echo -n "\\begin{code}[hide] occurences: "
cat *.lagda | grep -o "begin{code}\[hide\]" | wc -l
echo -n "%TC:ignore occurences:          "
cat *.lagda | grep -o "%TC:ignore" | wc -l
echo -n "%TC:endignore occurences:       "
cat *.lagda | grep -o "%TC:endignore" | wc -l
