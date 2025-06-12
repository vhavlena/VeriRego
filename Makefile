
BUILD_DIR=build

# List of binaries and their corresponding cmd directories
BINARIES = type_analysis
CMD_DIRS = type_analysis

.PHONY: all build test clean install

all: build

build:
	@echo "Building..."
	@mkdir -p $(BUILD_DIR)
	@for dir in $(CMD_DIRS); do \
	  go build -o $(BUILD_DIR)/$$dir ./cmd/$$dir/main.go; \
	done

test:
	@echo "Running tests..."
	@go test ./...

clean:
	@echo "Cleaning..."
	@rm -rf $(BUILD_DIR)

# Optional: Add install target to copy all binaries to system path
install: build
	@echo "Installing..."
	@for dir in $(CMD_DIRS); do \
	  cp $(BUILD_DIR)/$$dir /usr/local/bin/; \
	done