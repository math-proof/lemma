# usage:
# bash rsync.sh --path gitlab/pip --host $host --reverse
# bash rsync.sh gitlab/pip --host $host --reverse
# to enable write permission recursively for remote path:
# find . -type d -name "__pycache__" -exec chmod -R 777 {} +
# to ignore mode change during rsync:
# git config core.fileMode false
# git config core.autocrlf false
# add something like : ssh-keygen -R "[js2.blockelite.cn]:14836" if Host key verification failed
boolean_options=(
  "reverse"
  "delete"
  "diff"
)
kwargs_options=(
  "path"
  "host"
  "port"
)
source $(dirname $0)/parse_options.sh
parse_args boolean_options kwargs_options "$@"
if [ -z "$path" ]; then
  path=${args[0]}
  if [ -z "$path" ]; then
    echo "path is required"
    exit 1
  fi
fi
if ! command -v rsync &> /dev/null; then
  apt update && apt install -y rsync
fi
id_rsa=~/.ssh/id_rsa
id_rsa_pub=~/.ssh/id_rsa.pub
if [[ ! -f "$id_rsa" ]] || [[ ! -f "$id_rsa_pub" ]]; then
  cat <<EOF
ERROR: SSH keypair not found. Run: ssh-keygen -t rsa -b 4096 -f ~/.ssh/id_rsa
here is how to get the public key if you have the private key: ssh-keygen -y -f ~/.ssh/id_rsa > ~/.ssh/id_rsa.pub
EOF
  exit 1
fi
rsync="rsync -avzP --no-group --no-times"
[ "$delete" ] && rsync+=" --delete"
if [[ "$port" ]]; then
  ssh="ssh -p $port"
  export RSYNC_RSH="$ssh"
else
  ssh="ssh"
fi
path=${path%/}
if [[ "$path" == */* ]]; then 
  path_dir=${path%/*}
else 
  path_dir="."
fi
if [ "$reverse" ]; then
  real_path=$($ssh $host "readlink -f $path 2>/dev/null || echo $path")
  if [ -z "$real_path" ]; then
    echo "ERROR: remote path does not exist: $path"
    exit 1
  fi
  from_path=$host:$real_path
  to_path=$path_dir
  if [[ "$to_path" != /* ]]; then
    to_path=~/$to_path
  fi
  mkdir -p $to_path
else
  from_path=$path
  if [[ "$from_path" != /* ]]; then
    from_path=~/$from_path
  fi
  $ssh $host "mkdir -p $path_dir"
  to_path=$host:$path_dir
fi
if [ "$diff" ]; then
  files=()
  local_path=$path
  if [[ "$local_path" != /* ]]; then
    local_path=~/$local_path
  fi
  remote_home=$($ssh $host 'echo $HOME')
  remote_path=$path
  if [[ "$remote_path" != /* ]]; then
    remote_path="$remote_home/$remote_path"
  fi
  exclude="--exclude=__pycache__ --exclude=*.log --exclude=*.out --exclude=*.lock"
  while read -r line; do
    # Extract file paths
    if [[ "$line" == skipping\ * ]]; then
      continue
    fi

    file=$(echo "$line" | awk '{print $2}')
    # Compare file contents
    #   echo "Comparing $file"
    files+=("$file")
  done < <(rsync -rin --exclude=.git $exclude $local_path/ $host:$remote_path/)

  for file in "${files[@]}"; do
    echo -e "\e[33mComparing $file\e[0m"
    diff $local_path/$file <($ssh $host "cat $remote_path/$file" 2>/dev/null)
  done
  # $rsync --exclude='* -> *' $exclude $from_path $to_path
else
  $rsync $from_path $to_path
fi