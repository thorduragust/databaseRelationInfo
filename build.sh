#!/bin/bash
FILENAME=databaseRelationInfo.c
OUTPUT=databaseRelationInfo

gcc $FILENAME -o $OUTPUT

if [[ "$?" == "0" ]]; then
	./$OUTPUT
fi
