BUILD_FOLDER=./build
NEARLEYC=nearleyc

LOCAL_SRC = $(shell find ./src/ -type f -name '*.js')
BUILD_SRC = $(patsubst ./%, $(BUILD_FOLDER)/%, $(LOCAL_SRC))

LOCAL_RESSOURCES = $(shell find ./ressources/ -type f)
BUILD_RESSOURCES = $(patsubst ./%, $(BUILD_FOLDER)/%, $(LOCAL_RESSOURCES))

LOCAL_EXAMPLES = $(shell find ./examples/ -type f  -name '*.dk')
BUILD_EXAMPLES = $(patsubst ./%, $(BUILD_FOLDER)/%, $(LOCAL_EXAMPLES))


# Compile with "make Q=" to display the commands that are run.
Q = @

.PHONY: all build clean rebuild

all: build

build: $(BUILD_SRC) $(BUILD_RESSOURCES) $(BUILD_EXAMPLES) $(BUILD_FOLDER)/index.html
	@echo "Build done !"

clean:
	$(Q)rm -rf "$(BUILD_FOLDER)"
	@echo "Clean done !"

rebuild: clean build

$(BUILD_FOLDER)/%: %
	$(Q)mkdir -m 775 -p "$(@D)"
	$(Q)cp "$<" "$@"
	$(Q)chmod a+rx "$@"

lib/grammar.js: lib/grammar.ne
	$(Q)cd lib
	$(Q)$(NEARLEYC) grammar.ne > grammar.js
