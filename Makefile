BINARY_NAME=verirego
BUILD_DIR=build
CMD_DIR=cmd/verirego

.PHONY: all build test clean

all: build

build:
	@echo "Building..."
	@mkdir -p $(BUILD_DIR)
	@go build -o $(BUILD_DIR)/$(BINARY_NAME) $(CMD_DIR)/main.go

test:
	@echo "Running tests..."
	@go test ./...

clean:
	@echo "Cleaning..."
	@rm -rf $(BUILD_DIR)

# Optional: Add install target to copy binary to system path
install: build
	@echo "Installing..."
	@cp $(BUILD_DIR)/$(BINARY_NAME) /usr/local/bin/