#!/bin/zsh

set -e

emulate -L zsh

scriptName=$(readlink -f $0)

function usage {
    cat 1>&2 <<EOF
Usage: ${scriptName:t} TARGET_PROGRAM
EOF
    
    exit 1
}

#========================================

zparseopts -D -K x=o_xtrace i:=o_image

if (($#o_image)); then
    imageName=${${o_image[2]}#=}
else
    imageName=hkoba501/xhf-acceptance-inspection
fi

((ARGC)) || usage

target=$(readlink -f $1); shift

opts=(
    -v ${target:h}:${target:h}
    -v $PWD:$PWD
    -w $PWD
)

sudo=()
zmodload zsh/parameter
if ! (($+usergroups[docker])); then
    sudo=(sudo)
fi

((!$#o_xtrace)) || set -x

$sudo docker run -it $opts $imageName $target
