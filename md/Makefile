CHAPTER_DIR := ../LeanW26

MD_DIR := src

NAMES :=  Basic SUMMARY
MD_FILES := $(foreach item,$(NAMES), $(MD_DIR)/$(item).md)

CAT_NAMES := CartesianClosed Category BinaryProduct Exponential
CAT_FILES := $(foreach item,$(CAT_NAMES), $(MD_DIR)/Categories/$(item).md)

all: $(MD_FILES) $(CAT_FILES) 

$(MD_DIR)/%.md: $(CHAPTER_DIR)/%.lean 
	python3 dm.py $(CHAPTER_DIR)/$*.lean > $@

$(MD_DIR)/Categories/%.md: $(CHAPTER_DIR)/Categories/%.lean 
	python3 dm.py $(CHAPTER_DIR)/Categories/$*.lean > $@	


deploy:
	rm -rf ../docs
	cp -r book ../docs

clean:
	rm -f $(MD_DIR)/*.md \
	      $(MD_DIR)/Categories/*.md \



