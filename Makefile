# Makefile for compiling Literate Agda to PDF using XeLaTeX

AGDA=agda
LATEX=xelatex  # Use XeLaTeX instead of pdfLaTeX
TARGET_DIR=latex

# Extracts just the filename without path and extension
FILE_NAME=$(basename $(FILE) .lagda)

# Default rule to compile a .lagda file
make: $(FILE)
	@mkdir -p $(TARGET_DIR)
	$(AGDA) --latex $< --latex-dir=$(TARGET_DIR)
	cd $(TARGET_DIR) && $(LATEX) $(FILE_NAME).tex && cd ..

# Clean rule to remove generated files, including .lagdai files
clean:
	rm -rf $(TARGET_DIR)
	find src/ -name "*.lagdai" -type f -delete

# Ensure a file is provided
$(FILE):
	@echo "Usage: make FILE=src/part1/induction-p01-02.lagda"
	@exit 1