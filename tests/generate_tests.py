import sys

if __name__ == "__main__":

    test_name = sys.argv[1]
    start = int(sys.argv[2])
    end = int (sys.argv[3])

    for i in range(start, end+1):
        f_rkt = open(f"./{test_name}_test_{i}.rkt", "w")
        f_in = open(f"./{test_name}_test_{i}.in", "w")
        f_rkt.close()
        f_in.close()