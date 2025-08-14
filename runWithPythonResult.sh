agda_result="$(agda --compile Implementations/FFT.agda 1> /dev/null && ./FFT)"
echo "$agda_result"
nix-shell --command 'python ./FFT.py "'"$(echo "$agda_result" | grep "Flat Tensor:")"'"'
