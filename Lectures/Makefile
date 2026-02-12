.PHONY: rocq clean

ROCQ=rocq compile -q

rocq:
	$(ROCQ) W1.v
	$(ROCQ) W2.v
	$(ROCQ) W3.v
	$(ROCQ) W4a.v
	$(ROCQ) W4b.v


clean:
	rm -f *.vo *.glob *.vok *.vos
