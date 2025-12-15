#!/bin/bash

WATCH_DIR=".." 

echo "Watching directory: $WATCH_DIR for file changes. Running 'make $MAKE_TARGET' on change..."

while inotifywait -r -e modify,create,delete,move "$WATCH_DIR"; do
    echo "File change detected! Running make..."
    make 
done