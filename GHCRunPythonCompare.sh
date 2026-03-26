agda_result="$(make CompileGHC && ./bin/FFT)"
# echo "$agda_result"
# nix-shell --command 'python ./GHCCompareFFT.py "'"$(echo "$agda_result" | grep "Flat Tensor:")"'"'
# python3 ./GHCCompareFFT.py "$(echo "$agda_result" | grep "Flat Tensor:")"
python3 ./FFT.py "$(echo "$agda_result")"
