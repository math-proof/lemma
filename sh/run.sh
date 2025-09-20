#!/bin/bash
if [ -z "$MYSQL_USER" ]; then
  echo "MYSQL_USER is not set, acquiring it from ~/.bash_profile"
  source ~/.bash_profile
fi

while true; do
    # Run the Python program with a timeout of 1 minute (60 seconds)
    timeout 120 python run.py

    # Capture the exit status of the timeout command
    exit_status=$?

    # Check the exit status
    if [ $exit_status -eq 124 ]; then
        echo "Python program was halted because it took more than 2 minute."
    elif [ $exit_status -eq 0 ]; then
        echo "Python program completed within the time limit."
        break
    else
        echo "An error occurred. Exit status: $exit_status"
        continue
    fi
done

echo "Please enter any key to continue"
read user_input

python -c "exec(open('./util/hierarchy.py').read())"
python -c "exec(open('./util/function.py').read())"