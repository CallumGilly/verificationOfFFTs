import numpy as np
import sys


# ( 4.0 + 2.0 i ) => 4.0+2.0j
def parse_complex(s):
    s = s.strip("() ").replace(" ", "")
    s = s.replace("i", "j")
    try:
        return complex(s)
    except ValueError:
        raise ValueError(f"Could not parse complex number: '{s}'")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Input csv string not provided")
        sys.exit(1)

    try:
        cli_input = sys.argv[1].split("[")[1].split("]")[0]

        input_arr = [parse_complex(x) for x in cli_input.split(",")]

        np_arr = np.array(input_arr, dtype=complex)

        FFT_applied = np.fft.fft(np_arr)

        print("Python FFT Result: [", end="")
        print(FFT_applied[0], end="")

        for x in FFT_applied[1:]:
            print(", ", x, sep="", end="")

        print("]")

    except ValueError:
        print("Invalid input form")

