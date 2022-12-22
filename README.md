# msbackup-recover
recovers passwords from DOS 6.xx MSBACKUP backup catalogs

## setup
1. download or clone this repo
2. have python3 installed
3. install [z3](https://github.com/Z3Prover/z3) with `pip install z3-solver`

## usage
./msbackup-recovery [path to catalog file]

catalog files end with numbers like .001 or .002, etc. if you have a floppy backup you will probably want to first image your floppies, then pull the first catalog file off to run with this software.

## how it works
MSBACKUP.EXE is a backup program for MS-DOS. In the DOS 6.xx days, MSBACKUP provided the ability to password-protect your backups.

The password is "hashed" and stored in the header for the backup catalog, but files are not encrypted or modified. Technically, a restoration from a password-protected backup is possible by fiddling with the file headers.

However, I thought it would be more fun to reverse engineer the password hashing algorithm and write something that cracks it.

The password hash is a 10-byte ASCII string stored at offset 0x61 in catalogs created by this version of MSBACKUP. If there is no password, this area will be null.

The password provided by the user is a maximum of 8 characters, and only supports visible ASCII range (excluding spaces). If the password is less than 8 characters, it will be padded out with spaces.

The password hash is generated by a series of XOR's that are effected on the password provided by the user:

| Hash character   | Value                         | Flag if clamped |
| ---------------- | ------------------------------| ----------------|
| 0                | pass[0] ^ pass[1]             | flag 1 &#124; 1 |
| 1                | pass[2] ^ pass[3]             | flag 1 &#124; 2 |
| 2                | pass[4] ^ pass[5]             | flag 1 &#124; 4 |
| 3                | pass[6] ^ pass[7]             | flag 1 &#124; 8 |
| 4                | pass[3] ^ pass[1]             | flag 2 &#124; 1 |
| 5                | pass[5] ^ pass[7]             | flag 2 &#124; 2 |
| 6                | pass[3] ^ pass[7]             | flag 2 &#124; 4 |
| 7                | pass[7] ^ (pass[0] ^ pass[1]) | flag 2 &#124; 8 |
| 8                | flag 1, init 0x40             |                 |
| 9                | flag 2, init 0x40             |                 |

If any of the output characters is unprintable (including spaces), i.e., < 0x21, it is then clamped by OR'ing its value with 0x40 (@). If a character is clamped, a bitflag is set (see table above). This clamping can result in collisions since it involves a destructive OR.

## cracking

Since we know that the hash is made up of a network of XOR's, and sometimes OR's, it's possible to greatly reduce the keyspace vs. searching via brute force. I started by writing something that enumerated all possible pairs of characters for a given pair of output characters, but a couple of friends suggested I try doing this with a sat solver like Google's OR-Tools or Microsoft's Z3. I ended up using Z3 since that's what my friend was familiar with, who graciously helped demonstrate how to get things going.

By handing Z3 a list of constraints, it solves the password for us. It sometimes will find collisions where a password is technically mathematically possible, but won't work when entered into MSBACKUP. This is because MSBACKUP runs the same hash routine for comparing password hashes, and isn't actually checking the math of which characters are which. So, this script will also do a forward hash and filter the output from Z3 to only include passwords that will actually work in MSBACKUP. Interestingly there may still be collisions that generate multiple passwords for a given catalog, though I haven't seen any yet.

## contact

in the off chance a single person on earth finds a use for this, please contact me by filing an issue. i cannot imagine there are many of you out there. hope this helps though
