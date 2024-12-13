  sed 's/\[/\n[\n/g' \
  | sed 's/\]/\n]/g' \
  | awk '
    BEGIN{indent=-1}
    ($1 ~ /^\[/ ){indent+=1}
    {myLine=""}
    {
      for (i = 0; i < indent; i++)
        myLine = myLine "\t"
    }
    {print myLine $0}
    ($1 ~ /^\]/ ){indent-=1}
    '
