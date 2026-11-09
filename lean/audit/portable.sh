# Helpers shared by the audit scripts; they are sourced, not run. They need bash 3.2 or later
# and work on macOS and Linux.
#
#   sha256 FILE                  print the SHA-256 of FILE (with sha256sum, shasum or openssl)
#   run_measured OUT ERR CMD...  run CMD at low priority, stdout to OUT and stderr to ERR; where
#                                /usr/bin/time exists, it also writes the peak memory into ERR
#                                (BSD time -l on macOS, GNU time -v on Linux)
#   peak_gb ERR                  print the peak memory recorded in ERR, in GiB, or n/a
#
# Set TIME_BIN to use another time program.

sha256() {
  if command -v sha256sum > /dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  elif command -v shasum > /dev/null 2>&1; then
    shasum -a 256 "$1" | cut -d' ' -f1
  else
    openssl dgst -sha256 -r "$1" | cut -d' ' -f1
  fi
}

TIME_BIN=${TIME_BIN:-/usr/bin/time}
TIME_CMD=()
if [ -x "$TIME_BIN" ]; then
  if "$TIME_BIN" -l true > /dev/null 2>&1; then
    TIME_CMD=("$TIME_BIN" -l)   # BSD time: maximum resident set size in bytes
  elif "$TIME_BIN" -v true > /dev/null 2>&1; then
    TIME_CMD=("$TIME_BIN" -v)   # GNU time: maximum resident set size in kbytes
  fi
fi
NICE_CMD=()
if command -v nice > /dev/null 2>&1; then
  NICE_CMD=(nice -n 10)
fi

run_measured() {
  local out=$1 err=$2
  shift 2
  # ${a[@]+"${a[@]}"} expands an empty array without an error under set -u in bash 3.2
  ${NICE_CMD[@]+"${NICE_CMD[@]}"} ${TIME_CMD[@]+"${TIME_CMD[@]}"} "$@" > "$out" 2> "$err"
}

peak_gb() {
  local p
  p=$(awk '/Maximum resident set size \(kbytes\)/ { printf "%.2f", $NF / 1048576; exit }
           /maximum resident set size/ { printf "%.2f", $1 / 1073741824; exit }' "$1" 2> /dev/null)
  echo "${p:-n/a}"
}
