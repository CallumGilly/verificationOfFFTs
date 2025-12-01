import numpy as np
import csv
import sys


# ( 4.0 + 2.0 i ) => 4.0+2.0j
def parse_complex(s):
    pass
    # s = s.strip("() ").replace(" ", "")
    # s = s.replace("i", "j")
    # try:
    #     return complex(s)
    # except ValueError:
    #     raise ValueError(f"Could not parse complex number: '{s}'")

if __name__ == "__main__":
    input = list(csv.DictReader(sys.stdin))

    input_arr = np.array(
                    [float(x[" Input-Real"]) + (1j * float(x[" Input-Imag"])) for x in input], 
                    dtype=complex
                )
    CDFT_arr = np.array(
                    [float(x[" DFT-Real"]) + (1j * float(x[" DFT-Imag"])) for x in input], 
                    dtype=complex
                )
    CFFT_arr = np.array(
                    [float(x[" FFT-Real"]) + (1j * float(x[" FFT-Imag"])) for x in input], 
                    dtype=complex
                )

    NPFFT_applied = np.fft.fft(input_arr)

    results = np.stack([CDFT_arr, CFFT_arr, NPFFT_applied], axis=1)

    CDFT_CFFT_Real_Diff = 0
    CDFT_CFFT_Imag_Diff = 0
    CDFT_PFFT_Real_Diff = 0
    CDFT_PFFT_Imag_Diff = 0
    CFFT_PFFT_Real_Diff = 0
    CFFT_PFFT_Imag_Diff = 0
    count=0

    for row in results:
        CDFT_CFFT_Real_Diff += abs(np.real(row[0]) - np.real(row[1]))
        CDFT_CFFT_Imag_Diff += abs(np.imag(row[0]) - np.imag(row[1]))
    
        CDFT_PFFT_Real_Diff += abs(np.real(row[0]) - np.real(row[2]))
        CDFT_PFFT_Imag_Diff += abs(np.imag(row[0]) - np.imag(row[2]))

        CFFT_PFFT_Real_Diff += abs(np.real(row[1]) - np.real(row[2]))
        CFFT_PFFT_Imag_Diff += abs(np.imag(row[1]) - np.imag(row[2]))

        count += 1

    print("CDFT_CFFT_Real_Diff: ", CDFT_CFFT_Real_Diff / count)
    print("CDFT_CFFT_Imag_Diff: ", CDFT_CFFT_Imag_Diff / count)
    print("CDFT_PFFT_Real_Diff: ", CDFT_PFFT_Real_Diff / count)
    print("CDFT_PFFT_Imag_Diff: ", CDFT_PFFT_Imag_Diff / count)
    print("CFFT_PFFT_Real_Diff: ", CFFT_PFFT_Real_Diff / count)
    print("CFFT_PFFT_Imag_Diff: ", CFFT_PFFT_Imag_Diff / count)



    


    


    #if len(sys.argv) < 2:
    #    print("Input csv string not provided")
    #    sys.exit(1)

    #try:
    #    cli_input = sys.argv[1].split(",");
    #    print(cli_input)

        # input_arr = [parse_complex(x) for x in cli_input.split(",")]

        # np_arr = np.array(input_arr, dtype=complex)

        # FFT_applied = np.fft.fft(np_arr)

        # print("Python FFT Result: [", end="")
        # print(FFT_applied[0], end="")

        # for x in FFT_applied[1:]:
        #     print(", ", x, sep="", end="")

        # print("]")

    #except ValueError:
    #    print("Invalid input form")

