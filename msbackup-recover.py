#!/usr/bin/env python3
# requires z3 (pip install z3)
import argparse
import sys
from z3 import *

# reimplementation of the code that runs in msbackup
def encrypt(s):
  # pad to 8 characters with spaces at the end
  s = s.ljust(8, " ")

  s = bytearray(s, 'ascii')

  # output is 10 characters, with last 2 chars (the bitflags) initialized to @ / 0x40
  out_s = "        @@"
  out_s = bytearray(out_s, 'ascii')

  # generic helper function to delight and confuse
  def transform_chars(in1, in2, outpos):
    out = in1 ^ in2
    if out < 0x21:
      # if out of visible range, clamp to visible range by OR'ing with 0x40 (@)
      out = out | 0x40
      # update bitflags if clamped
      if outpos <= 3:
        out_s[8] = out_s[8] | (2 ** outpos)
      else:
        out_s[9] = out_s[9] | (2 ** (outpos - 4))
    return out

  # FIRST OUTPUT CHARACTER -- xor(1st,2nd)
  out_s[0] = transform_chars(s[0], s[1], 0)

  # SECOND OUTPUT CHARACTER -- xor(3rd,4th)
  out_s[1] = transform_chars(s[2], s[3], 1)
  
  # THIRD OUTPUT CHARACTER -- xor(5th,6th)
  out_s[2] = transform_chars(s[4], s[5], 2)

  # FOURTH OUTPUT CHARACTER -- xor(7th,8th)
  out_s[3] = transform_chars(s[6], s[7], 3)

  # FIFTH OUTPUT CHARACTER -- xor(4th,2nd)
  out_s[4] = transform_chars(s[3], s[1], 4)

  # SIXTH OUTPUT CHARACTER -- xor(6th,8th)
  out_s[5] = transform_chars(s[5], s[7], 5)

  # SEVENTH OUTPUT CHARACTER -- xor(4th,8th)
  out_s[6] = transform_chars(s[3], s[7], 6)

  # EIGHTH OUTPUT CHARACTER -- xor(8th,xor(1st,2nd))
  out_s[7] = transform_chars(s[7], s[0] ^ s[1], 7)

  return out_s.decode('ascii')

# helper function to get all possible solutions from z3
# see https://github.com/Z3Prover/z3/issues/5765#issuecomment-1009760596
def all_smt(s, initial_terms):
    def block_term(s, m, t):
        s.add(t != m.eval(t, model_completion=True))
    def fix_term(s, m, t):
        s.add(t == m.eval(t, model_completion=True))
    def all_smt_rec(terms):
        if sat == s.check():
           m = s.model()
           yield m
           for i in range(len(terms)):
               s.push()
               block_term(s, m, terms[i])
               for j in range(i):
                   fix_term(s, m, terms[j])
               yield from all_smt_rec(terms[i:])
               s.pop()   
    yield from all_smt_rec(list(initial_terms))

def solve(hash):
    s = Solver()
    pw = [BitVec('pw' + str(n), 8) for n in range(8)]
    cipher = [BitVec('in' + str(n), 8) for n in range(10)]
    for i, v in enumerate(cipher):
        s.add(v == ord(hash[i]))
    for c in pw:
        s.add(c >= 0x20, c <= 0x7e)
    s.add(Or(cipher[0] == pw[0] ^ pw[1], cipher[0] == 0x40 | (pw[0] ^ pw[1])))
    s.add(Or(cipher[1] == pw[2] ^ pw[3], cipher[1] == 0x40 | (pw[2] ^ pw[3])))
    s.add(Or(cipher[2] == pw[4] ^ pw[5], cipher[2] == 0x40 | (pw[4] ^ pw[5])))
    s.add(Or(cipher[3] == pw[6] ^ pw[7], cipher[3] == 0x40 | (pw[6] ^ pw[7])))
    s.add(Or(cipher[4] == pw[3] ^ pw[1], cipher[4] == 0x40 | (pw[3] ^ pw[1])))
    s.add(Or(cipher[5] == pw[5] ^ pw[7], cipher[5] == 0x40 | (pw[5] ^ pw[7])))
    s.add(Or(cipher[6] == pw[3] ^ pw[7], cipher[6] == 0x40 | (pw[3] ^ pw[7])))
    s.add(Or(cipher[7] == pw[7] ^ (pw[0] ^ pw[1]), cipher[7] == 0x40 | (pw[7] ^ (pw[0] ^ pw[1]))))
    s.add(Or(And(cipher[8] & 1 == 1, pw[0] ^ pw[1] < 0x21), And(cipher[8] & 1 == 0, pw[0] ^ pw[1] >= 0x21)))
    s.add(Or(And(cipher[8] & 2 == 2, pw[2] ^ pw[3] < 0x21), And(cipher[8] & 2 == 0, pw[2] ^ pw[3] >= 0x21)))
    s.add(Or(And(cipher[8] & 4 == 4, pw[4] ^ pw[5] < 0x21), And(cipher[8] & 4 == 0, pw[4] ^ pw[5] >= 0x21)))
    s.add(Or(And(cipher[8] & 8 == 8, pw[6] ^ pw[7] < 0x21), And(cipher[8] & 8 == 0, pw[6] ^ pw[7] >= 0x21)))
    s.add(Or(And(cipher[9] & 1 == 1, pw[3] ^ pw[1] < 0x21), And(cipher[9] & 1 == 0, pw[3] ^ pw[1] >= 0x21)))
    s.add(Or(And(cipher[9] & 2 == 2, pw[5] ^ pw[7] < 0x21), And(cipher[9] & 2 == 0, pw[5] ^ pw[7] >= 0x21)))
    s.add(Or(And(cipher[9] & 4 == 4, pw[3] ^ pw[7] < 0x21), And(cipher[9] & 4 == 0, pw[3] ^ pw[7] >= 0x21)))
    s.add(Or(And(cipher[9] & 8 == 8, (pw[7] ^ (pw[0] ^ pw[1])) < 0x21),
          And(cipher[9] & 8 == 0, (pw[7] ^ (pw[0] ^ pw[1]) >= 0x21))))

    results = list(all_smt(s, pw + cipher))
    candidates = []
    for r in results:
      candidates.append(''.join(chr(r[pw[i]].as_long()) for i in range(8)))
    
    # collisions may have been found. they satisfy the math constraints for the hash, but the deterministic
    # hash generation function will not generate them, and thus the passwords won't work. filter these out 
    # by running the hash function manually
    out = [c for c in candidates if encrypt(c) == hash]
    
    if len(out) == 0:
      print(f"unable to solve for hash {hash} -- no candidates were reflexive. list of candidates:")
      print(candidates)
      return False

    return out

def get_hash_from_catalog(file):
  try:
    with open(file, 'rb') as f:
      f.seek(1)
      version_string = f.read(13).decode('ascii')
      if version_string != "NORTON Ver 1E" and version_string != "NORTON Ver 2A":
        print("Backup file does not appear to be from MSBACKUP (DOS 6.xx era). Make sure you are using the first catalog file, usually a file ending in .001")
        return False

      f.seek(0x61)
      hash = f.read(10)
      if hash == b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00":
        print("File does not appear to be password protected (password field is empty)")
        return False

      return hash.decode('ascii')
  except:
    print("Error: problem reading catalog file. Does it exist, and do you have permission to read it? If yes and yes, report this bug.")
    return False

if __name__ == '__main__':
  parser = argparse.ArgumentParser(
    prog = 'msbackup-recover',
    description = 'given a password-protected msbackup catalog file, will attempt to recover the password'
  )
  parser.add_argument('catalog_filename')
  args = parser.parse_args()
  catalog_file = args.catalog_filename
  hash = get_hash_from_catalog(catalog_file)
  if not hash:
    sys.exit(1)
  pws = solve(hash)
  if not pws:
    sys.exit(1)
  if len(pws) == 1:
    print(f"Password for catalog file {catalog_file}: {pws[0]}")
  else:
    print(f"Working passwords for catalog file {catalog_file}:")
    print("\n".join(pws))

  sys.exit(0)

"""
test_cases = [
    ("S@Y@Y@P3KC", "zippy   "),
    ("RB@@U@F2OC", "asdf    "),
    ("GE@@D@K'OC", "honk    "),
    ("@@@@@@@aOG", "aaaaaaaa"),
    ("@@@@@@@~OG", "~~~~~~~~"),
    ("@@@@@@@@OG", "@@@@@@@@")
]

for cipher, expected in test_cases:
    print(cipher, expected, solve(cipher))
"""
