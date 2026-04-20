CHAPTER_DIR := ../LeanW26
MD_DIR := src
SUBVERSO_DIR := slider/dist/subverso

LEAN_DIRS := $(wildcard $(CHAPTER_DIR)/*)
MD_DIRS :=  $(patsubst $(CHAPTER_DIR)/%,$(MD_DIR)/%,$(LEAN_DIRS))
SUBVERSO_DIRS := $(patsubst $(CHAPTER_DIR)/%,$(SUBVERSO_DIR)/%,$(LEAN_DIRS))

LEAN_FILES := $(wildcard $(CHAPTER_DIR)/*/*.lean)
MD_FILES := $(patsubst $(CHAPTER_DIR)/%.lean,$(MD_DIR)/%.md,$(LEAN_FILES))
SUBVERSO_FILES := $(patsubst $(CHAPTER_DIR)/%.lean,$(SUBVERSO_DIR)/%.json,$(LEAN_FILES))

all: dirs $(MD_FILES) $(SUBVERSO_FILES)

$(MD_DIR)/%.md: $(CHAPTER_DIR)/%.lean | dirs
	python3 dm.py $(CHAPTER_DIR)/$*.lean > $@

$(SUBVERSO_DIR)/%.json: $(CHAPTER_DIR)/%.lean | dirs
	cd .. && lake exe subverso-extract-mod LeanW26.$(subst /,.,$*) md/$@

dirs: $(MD_DIRS) $(SUBVERSO_DIRS)

slider/src:
	mkdir -p $@

$(SUBVERSO_DIR):
	mkdir -p $@

$(MD_DIRS): | slider/src
	mkdir -p $@

$(SUBVERSO_DIRS): | $(SUBVERSO_DIR)
	mkdir -p $@

show: 
	echo $(MD_DIRS)
	echo $(MD_FILES)

clean:
	rm -r $(MD_DIR)/*

deploy:
	cd slider && bash deploy.sh
serve:
	python -m http.server 8000 --directory slider/dist
