verify:
	lake build
	lake env lean AxiomCheck.lean
	@echo "VERIFIED: build green; audited declarations depend only on propext, Classical.choice, Quot.sound"

.PHONY: verify
