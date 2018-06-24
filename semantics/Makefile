export K_OPTS := -Xmx2048m
KOMPILE = kompile

C11_TRANSLATION_FILES = $(wildcard *.k) \
	$(wildcard language/translation/*.k) $(wildcard language/translation/*/*.k) \
	$(wildcard language/common/*.k) $(wildcard language/common/*/*.k)
	
C11_FILES = $(wildcard *.k) \
	$(wildcard language/execution/*.k) $(wildcard language/execution/*/*.k) \
	$(wildcard language/common/*.k) $(wildcard language/common/*/*.k) \
	$(wildcard library/*.k)

C11_NON_FILES = $(wildcard *.k) \
	$(wildcard language/execution2/*.k) $(wildcard language/execution2/*/*.k) \
	$(wildcard language/common/*.k) $(wildcard language/common/*/*.k) \
	$(wildcard library/*.k) 

K_CLEAN_FILES = .k c11-translation-kompiled c11-kompiled c11-non-kompiled c11-nd-kompiled c11-nd-thread-kompiled c11-nond-kompiled

.PHONY: default all fast nd thread clean

default: fast

c11-translation-kompiled: $(C11_TRANSLATION_FILES)
	@echo "Kompiling the static C semantics..."
	@$(KOMPILE) c11-translation.k -d "c11-translation-kompiled" -w all -v
	@touch c11-translation-kompiled

c11-kompiled: $(C11_FILES)
	@echo "Kompiling the dynamic C semantics..."
	@$(KOMPILE) c11.k -d "c11-kompiled" -w all -v --transition "interpRule"
	@touch c11-kompiled

c11-non-kompiled: $(C11_NON_FILES)
	@echo "Kompiling the dynamic C semantics non-determinism..."
	@$(KOMPILE) c11-non.k -d "c11-non-kompiled" -w all -v --transition "interpRule"
	@touch c11-non-kompiled

c11-nd-kompiled: $(C11_FILES)
	@echo "Kompiling the dynamic C semantics with update non-determinism..."
	@$(KOMPILE) c11.k -d "c11-nd-kompiled" -w all -v --transition "update","finish-update" #--superheat "addition"
	@touch c11-nd-kompiled

c11-nond-kompiled: $(C11_FILES)
	@echo "Kompiling the dynamic C semantics with update non-determinism..."
	@$(KOMPILE) c11-non.k -d "c11-nond-kompiled" -w all -v --transition "update","finish-update" #--superheat "addition"
	@touch c11-nond-kompiled

c11-nd-thread-kompiled: $(C11_FILES)
	@echo "Kompiling the dynamic C semantics with thread-interleaving non-determinism..."
	@$(KOMPILE) c11.k -d "c11-nd-thread-kompiled" -v --transition "observable ndtrans ndthread"
	@touch c11-nd-thread-kompiled

all: fast nd thread

fast: c11-translation-kompiled c11-kompiled c11-non-kompiled c11-nond-kompiled

nd: c11-nd-kompiled

thread: c11-nd-thread-kompiled

clean:
	@-rm -rf $(K_CLEAN_FILES)

