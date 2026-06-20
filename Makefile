# crud-cli — notcurses front end for the Claude Code engine
PKG_CONFIG ?= pkg-config
CC        ?= cc
CFLAGS    ?= -O2 -Wall -Wextra
NC_CFLAGS := $(shell $(PKG_CONFIG) --cflags notcurses-core)
NC_LIBS   := $(shell $(PKG_CONFIG) --libs notcurses-core)

# modular build (see ARCHITECTURE.md §11 for the module map)
SRCS := src/crud-cli.c src/json.c

crud-cli: $(SRCS) src/json.h
	$(CC) $(CFLAGS) $(NC_CFLAGS) -o $@ $(SRCS) $(NC_LIBS) -lpthread

# AddressSanitizer + UBSan debug build (separate binary so it never clobbers the release one).
# Run: make asan && ./crud-cli-asan   — surfaces use-after-free, overflow, leaks, UB at runtime.
ASAN_FLAGS := -O1 -g -Wall -Wextra -fsanitize=address,undefined -fno-omit-frame-pointer -fno-sanitize-recover=all
asan: crud-cli-asan
crud-cli-asan: $(SRCS) src/json.h
	$(CC) $(ASAN_FLAGS) $(NC_CFLAGS) -o $@ $(SRCS) $(NC_LIBS) -lpthread

# P1 protocol spike (headless, no UI)
p1: spikes/p1_perm.c
	$(CC) $(CFLAGS) -o spikes/p1_perm spikes/p1_perm.c

# install — system-wide to $(PREFIX)/bin (default /usr/local). For /usr: `sudo make install PREFIX=/usr`.
# DESTDIR is honored for packaging (e.g. PKGBUILD: make install DESTDIR="$pkgdir" PREFIX=/usr).
PREFIX  ?= /usr/local
BINDIR  ?= $(PREFIX)/bin
install: crud-cli
	install -Dm755 crud-cli $(DESTDIR)$(BINDIR)/crud-cli

uninstall:
	rm -f $(DESTDIR)$(BINDIR)/crud-cli

clean:
	rm -f crud-cli crud-cli-asan spikes/p1_perm

.PHONY: clean asan install uninstall
