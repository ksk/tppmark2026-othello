# Build the source distribution. Recipes use POSIX sh.
SHELL = /bin/sh
.DEFAULT_GOAL := help

PYTHON ?= python3
ROCQ ?= rocq
OCAMLFIND ?=
BUILD_DIR ?= $(CURDIR)/_build
CERTIFICATE_SOURCE ?= $(CURDIR)
ARCHIVE_DIR ?=
JOBS ?= 4
LINK_JOBS ?= 1
INTERFACE_JOBS ?= 4
MODULE_TIMEOUT ?= 1800
FRESH ?= 0

BUILD_ARGS = --rocq "$(ROCQ)" --build-dir "$(BUILD_DIR)" \
  --certificate-source "$(CERTIFICATE_SOURCE)" --jobs "$(JOBS)" \
  --link-jobs "$(LINK_JOBS)" --interface-jobs "$(INTERFACE_JOBS)" \
  --module-timeout "$(MODULE_TIMEOUT)" \
  $(if $(OCAMLFIND),--ocamlfind "$(OCAMLFIND)") $(if $(filter 1,$(FRESH)),--fresh)

.PHONY: help check check-4x4 check-6x6 check-disk audit-6x6 kernel-6x6 \
  certificate-4x4 check-docs review-files check-certificate-files \
  check-archives unpack-certificates

help:
	@printf '%s\n' \
	  'make check              Build the 4x4 and 6x6 solutions from source' \
	  'make check-4x4          Build and independently check the 4x4 solution' \
	  'make check-6x6          Build the 6x6 solution and all certificate blocks' \
	  'make check-disk         Check free space before a full build' \
	  'make audit-6x6          Build 6x6 and audit all theorem dependencies' \
	  'make kernel-6x6         Build 6x6 and independently kernel-check the full result' \
	  'make certificate-4x4    Regenerate the 4x4 certificate' \
	  'make check-docs         Check the English and Japanese README pairs' \
	  'make review-files       Check the source package inventory' \
	  'make check-archives       Check the downloaded certificate archives' \
	  'make unpack-certificates  Check and unpack all certificate sources' \
	  'make check-certificate-files  Check the certificate sizes and SHA-256 hashes' \
	  'Options: ROCQ=/path/to/rocq BUILD_DIR=/path/to/build CERTIFICATE_SOURCE=/path/to/sources' \
	  '         OCAMLFIND=/path/to/ocamlfind ARCHIVE_DIR=/path/to/archives' \
	  '         JOBS=4 LINK_JOBS=1 INTERFACE_JOBS=4 MODULE_TIMEOUT=1800 FRESH=1'

check:
	$(PYTHON) build.py all $(BUILD_ARGS)

check-4x4:
	$(PYTHON) build.py 4x4 $(BUILD_ARGS)

check-6x6:
	$(PYTHON) build.py 6x6 $(BUILD_ARGS)

check-disk:
	$(PYTHON) build.py disk $(BUILD_ARGS)

audit-6x6:
	$(PYTHON) build.py audit-6x6 $(BUILD_ARGS)

kernel-6x6:
	$(PYTHON) build.py kernel-6x6 $(BUILD_ARGS)

certificate-4x4:
	$(PYTHON) generate_certificate.py

check-docs:
	$(PYTHON) distribution/check_docs.py

review-files: check-docs
	$(PYTHON) distribution/check_files.py

check-certificate-files:
	$(PYTHON) distribution/check_files.py --certificates --certificate-root "$(CERTIFICATE_SOURCE)"

check-archives:
	$(PYTHON) distribution/archive_files.py check --archive-dir "$(ARCHIVE_DIR)"

unpack-certificates:
	$(PYTHON) distribution/archive_files.py unpack --archive-dir "$(ARCHIVE_DIR)" \
	  --source-root "$(CERTIFICATE_SOURCE)"
