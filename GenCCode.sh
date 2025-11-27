agda --compile CGenerator.agda 1> /dev/null && ./CGenerator && clang-format -i generated/*
