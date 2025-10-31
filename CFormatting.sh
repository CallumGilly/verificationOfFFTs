  #   sed 's/\[/\n[\n/g' \
  # | sed 's/\]/\n]/g' \
    sed 's/[{]/\nOPEN-CURLY\n/g' \
  | sed 's/[}]/\nCLOSE-CURLY\n/g' \
  | sed 's/[(]/OPEN-BRACKET/g' \
  | sed 's/[)]/CLOSE-BRACKET/g' \
  | awk '
    BEGIN{indent=0}
    ($1 ~ /^OPEN-CURLY/ ){indent+=1}
    {myLine=""}
    {
      for (i = 0; i < indent; i++)
        myLine = myLine "\t"
    }
    {print myLine $0}
    ($1 ~ /^CLOSE-CURLY/ ){indent-=1}
    ' \
  | sed 's/OPEN-CURLY/{/g' \
  | sed 's/CLOSE-CURLY/}/g' \
  | sed 's/OPEN-BRACKET/(/g' \
  | sed 's/CLOSE-BRACKET/)/g' \
