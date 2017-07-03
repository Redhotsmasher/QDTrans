#!/bin/bash

red=`tput setaf 1`
green=`tput setaf 2`
yellow=`tput setaf 3`
reset=`tput sgr0`
count=0

#declare -a trans
#declare -a gcc
#declare -a clang
#declare -a run

#trans[0]=0
#gcc[0]=0
#clang[0]=0
#run[0]=0

for i in *.c ; do 
    [[ -f "$i" ]] || continue
    printf "Running test %d (%s)...\n" $count $i
    fn=${i%%.*}
    $HOME/clang-llvm/build/bin/qdtrans $i
    trans[$count]=$?
    gcc -g $i libqd_lock_lib.a -Iheaders/ -o $fn -lpthread
    gcc[$count]=$?
    clang -g $i libqd_lock_lib.a -Iheaders/ -o $fn -lpthread
    clang[$count]=$?
    ./$fn
    run[$count]=$?
    if [ ${gcc[$count]} -eq 0 -o ${gcc[$count]} -eq 0 ]
    then
        rm $fn
    fi
    mv -f $fn.noqd.bak $i
    rm $fn.qd.c
    count=$(( $count + 1 ))
done

printf "\n\nSummary:\n\n"
printf "╔══════════════╤═════╤═════╤═════╤═════╗\n"
printf "║   Filename   │Trans│ GCC │Clang│ Run ║\n"

count=0

for i in *.c ; do 
    [[ -f "$i" ]] || continue
    printf "╟──────────────┼─────┼─────┼─────┼─────╢\n"
    if [ ${trans[$count]} -ne 0 ]
    then
        printf "║%14s│${red}FAILS${reset}│${yellow} N/A ${reset}│${yellow} N/A ${reset}│${yellow} N/A ${reset}║\n" $i
    else
        if [ ${gcc[$count]} -eq 0 -a ${clang[$count]} -eq 0 ]
        then
            if [ ${run[$count]} -eq 0 ]
            then
                printf "║%14s│${green}WORKS${reset}│${green}WORKS${reset}│${green}WORKS${reset}│${green}WORKS${reset}║\n" $i
            else
                printf "║%14s│${green}WORKS${reset}│${green}WORKS${reset}│${green}WORKS${reset}│${red}FAILS${reset}║\n" $i
            fi
        else
            if [ ${gcc[$count]} -ne 0 -a ${clang[$count]} -ne 0 ]
            then
                printf "║%14s│${green}WORKS${reset}│${red}FAILS${reset}│${red}FAILS${reset}│${yellow} N/A ${reset}║\n" $i
            else
                if [ ${gcc[$count]} -ne 0 ]
                then
                    if [ ${run[$count]} -eq 0 ]
                    then
                        printf "║%14s│${green}WORKS${reset}│${red}FAILS${reset}│${green}WORKS${reset}│${green}WORKS${reset}║\n" $i
                    else
                        printf "║%14s│${green}WORKS${reset}│${red}FAILS${reset}│${green}WORKS${reset}│${red}FAILS${reset}║\n" $i
                    fi
                else
                    if [ ${run[$count]} -eq 0 ]
                    then
                        printf "║%14s│${green}WORKS${reset}│${green}WORKS${reset}│${red}FAILS${reset}│${green}WORKS${reset}║\n" $i
                    else
                        printf "║%14s│${green}WORKS${reset}│${green}WORKS${reset}│${red}FAILS${reset}│${red}FAILS${reset}║\n" $i
                    fi
                fi
            fi
        fi
    fi
    
    count=$(( $count + 1 ))
done

printf "╚══════════════╧═════╧═════╧═════╧═════╝\n"
