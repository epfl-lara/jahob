for i in $(seq 16); do
  echo seq$i
  ../../bin/formDecider.opt insertSeq$i -minasm -usedp z3:KeepRtrancl:Tree:NoTriggers > minAsmInsertSeq$i
done