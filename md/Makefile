CHAPTER_DIR := ../LeanW26

MD_DIR := src

NAMES :=  Basic SUMMARY
MD_FILES := $(foreach item,$(NAMES), $(MD_DIR)/$(item).md)

INTRO_NAMES := Lean
INTRO_FILES := $(foreach item,$(INTRO_NAMES), $(MD_DIR)/Introduction/$(item).md)

CAT_NAMES := CartesianClosed Category BinaryProduct Exponential TerminalObject Syntactic Latex
CAT_FILES := $(foreach item,$(CAT_NAMES), $(MD_DIR)/Categories/$(item).md)

all: $(MD_FILES) $(CAT_FILES)  $(INTRO_FILES) 

$(MD_DIR)/%.md: $(CHAPTER_DIR)/%.lean 
	python3 dm.py $(CHAPTER_DIR)/$*.lean > $@

$(MD_DIR)/Introduction/%.md: $(CHAPTER_DIR)/Introduction/%.lean 
	python3 dm.py $(CHAPTER_DIR)/Introduction/$*.lean > $@	

$(MD_DIR)/Categories/%.md: $(CHAPTER_DIR)/Categories/%.lean 
	python3 dm.py $(CHAPTER_DIR)/Categories/$*.lean > $@	

deploy:
	rm -rf ../docs
	cp -r book ../docs

clean:
	rm -f $(MD_DIR)/*.md \
	      $(MD_DIR)/Categories/*.md \
		  $(MD_DIR)/Introduction/*.md \



