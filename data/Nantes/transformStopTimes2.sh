fichier="stop_times.txt"
fichierout="adjacency2.txt"

cat $fichier | awk 'BEGIN{FS=" |,";old_trip=0;old_id=0;} {if ($1==old_trip) {print old_id "," $4 "," $1 "," $2 "," (substr($2,1,2)-start_hour)*60+(substr($2,4,2)-start_minute) ","  $5-1} else{start_hour=substr($2,1,2); start_minute=substr($2,4,2)};old_id=$4;old_trip=$1}' > $fichierout

