# Files from other repositories

lean/ contains the modules that the theorem needs from r1212-1642 and r1212-1658 and, through r1212-1642, from Tatarevic's repository. They are copied unchanged.

From [r1212-1642](https://github.com/YueMa0/r1212-1642) v1.0.0 (commit 95e1deeb9c69d5ca83de2aab3d2027e36a7177d0), directory lean/:

- lean/.gitignore, lean/lake-manifest.json, lean/lakefile.lean, lean/lean-toolchain;
- lean/RamseyIncrement/Basic.lean, Cone.lean, RamseyNumber.lean, SpecialLift.lean and Transport.lean;
- the 14 files in lean/RamseyIncrement/R1212/.

r1212-1642 took the first nine of these unchanged from https://github.com/milostatarevic/ramsey-increment-theorem, commit 36c15eca0c601be7b7f33e30ee6890f395d2e1ea (see the UPSTREAM.md of r1212-1642). They are covered by Tatarevic's MIT license; the copyright notice is in LICENSE. The files in R1212/ are new in r1212-1642.

From [r1212-1658](https://github.com/YueMa0/r1212-1658) (commit 0e999b5cd3648534d5adf067df78086b2f219148): lean/RamseyIncrement/R1658/Defect.lean, the defect lemma. The other modules of R1658/ are not needed and are not included.

New in this repository:

- lean/RamseyIncrement.lean, the root of the library; it imports only RamseyIncrement.R1661.Main;
- lean/AxiomAudit1661.lean and lean/Export1661.lean;
- lean/RamseyIncrement/R1661/, lean/gen/, lean/tools/ and lean/audit/.

To check that the copied files are unchanged:

```bash
git clone https://github.com/YueMa0/r1212-1642 /tmp/r1212-1642
git -C /tmp/r1212-1642 checkout 95e1deeb9c69d5ca83de2aab3d2027e36a7177d0
git clone https://github.com/YueMa0/r1212-1658 /tmp/r1212-1658
git -C /tmp/r1212-1658 checkout 0e999b5cd3648534d5adf067df78086b2f219148
cd lean
for f in .gitignore lake-manifest.json lakefile.lean lean-toolchain \
    RamseyIncrement/{Basic,Cone,RamseyNumber,SpecialLift,Transport}.lean \
    RamseyIncrement/R1212/*.lean; do
  cmp "/tmp/r1212-1642/lean/$f" "$f"
done
cmp /tmp/r1212-1658/lean/RamseyIncrement/R1658/Defect.lean RamseyIncrement/R1658/Defect.lean
```

The commands print nothing if the files are unchanged.
