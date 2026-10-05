# copied from https://github.com/kaldi-asr/kaldi/blob/master/egs/wsj/s5/utils/parse_options.sh

parse_args() {
  # $1 = name of boolean array, $2 = name of kwargs array, rest = "$@"
  if [ $# -lt 2 ]; then
    echo "parse_args requires: parse_args <boolean_array_name> <kwargs_array_name> -- [args...]"
    return 2
  fi
  # local -n boolean_options="$1"
  # local -n kwargs_options="$2"
  shift 2
  long=$(printf "%s: " "${kwargs_options[@]}")$(printf "%s " "${boolean_options[@]}")
  PARSED_OPTIONS=$(getopt -o h --long "$long" -- "$@")
  if [ $? -ne 0 ]; then
    echo "Error parsing options"
    exit 1
  fi
  eval set -- "$PARSED_OPTIONS"
  boolean_options=("${boolean_options[@]//-/_}")
  while true; do
    key="${1#--}"   # Remove the leading '--'
    if [ -z "$key" ]; then
      shift
      break
    fi

    if [ "$key" == "$1" ]; then
      echo "Error parsing options key = $key, \$1 = $1"
      exit 1
    fi

    key="${key//-/_}"  # Replace all '-' with '_'
    local is_boolean=false
    for opt in "${boolean_options[@]}"; do
      if [ "$opt" == "$key" ]; then
          declare -g "$key=true"
          shift
          is_boolean=true
          break
      fi
    done
    if ! $is_boolean; then
      declare -g "$key=$2"
      shift 2
    fi
  done
  # return the positional args
  declare -ga args=("$@")
}

rprint() {
  text="$1"
  # foreground color
  fg="$2"
  # background color (optional)
  bg="$3"
  # style: normal (default), bold, underline
  style="${4:-normal}"

  # Foreground colors
  case "$fg" in
    black)   code_fg=30 ;;
    red)     code_fg=31 ;;
    green)   code_fg=32 ;;
    yellow)  code_fg=33 ;;
    blue)    code_fg=34 ;;
    magenta) code_fg=35 ;;
    cyan)    code_fg=36 ;;
    white)   code_fg=37 ;;
    *)       code_fg=39 ;;   # default
  esac

  # Background colors
  case "$bg" in
    black)   code_bg=40 ;;
    red)     code_bg=41 ;;
    green)   code_bg=42 ;;
    yellow)  code_bg=43 ;;
    blue)    code_bg=44 ;;
    magenta) code_bg=45 ;;
    cyan)    code_bg=46 ;;
    white)   code_bg=47 ;;
    ""|none) code_bg=49 ;;   # default (no background)
    *)       code_bg=49 ;;
  esac

  # Styles
  case "$style" in
    bold)      code_style=1 ;;
    underline) code_style=4 ;;
    normal|*)  code_style=0 ;;
  esac

  echo -e "\033[${code_style};${code_fg};${code_bg}m${text}\033[0m"
}
