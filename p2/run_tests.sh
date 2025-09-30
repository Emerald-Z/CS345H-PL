#!/bin/bash

# Script to run all test files and compare with expected output
# Usage: ./run_tests.sh [timeout_seconds]

set -e  # Exit on any error

# Default timeout in seconds (can be overridden by command line argument)
TIMEOUT=${1:-5}

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check if fun executable exists
if [ ! -f "./fun" ]; then
    echo -e "${RED}Error: fun executable not found. Please run 'make fun' first.${NC}"
    exit 1
fi

# Test directory
TEST_DIR="cs345h_f25_p2a__tests"

if [ ! -d "$TEST_DIR" ]; then
    echo -e "${RED}Error: Test directory '$TEST_DIR' not found.${NC}"
    exit 1
fi

echo -e "${YELLOW}Running tests in $TEST_DIR with ${TIMEOUT}s timeout...${NC}"
echo "=================================="

# Counters
PASSED=0
FAILED=0
TOTAL=0

# Find all .fun files in the test directory
for fun_file in "$TEST_DIR"/*.fun; do
    if [ ! -f "$fun_file" ]; then
        continue
    fi
    
    # Get the base name without extension
    base_name=$(basename "$fun_file" .fun)
    ok_file="$TEST_DIR/$base_name.ok"
    
    # Check if corresponding .ok file exists
    if [ ! -f "$ok_file" ]; then
        echo -e "${YELLOW}Warning: No .ok file found for $base_name${NC}"
        continue
    fi
    
    TOTAL=$((TOTAL + 1))
    
    # Run the test
    echo -n "Testing $base_name... "
    
    # Create temporary output file
    temp_out=$(mktemp)
    
    # Run fun on the test file with timeout and capture output
    if timeout "$TIMEOUT" ./fun < "$fun_file" > "$temp_out" 2>&1; then
        # Compare with expected output
        if diff -q "$ok_file" "$temp_out" > /dev/null 2>&1; then
            echo -e "${GREEN}PASS${NC}"
            PASSED=$((PASSED + 1))
        else
            echo -e "${RED}FAIL${NC}"
            FAILED=$((FAILED + 1))
            echo -e "${RED}  Expected output:${NC}"
            cat "$ok_file" | sed 's/^/    /'
            echo -e "${RED}  Actual output:${NC}"
            cat "$temp_out" | sed 's/^/    /'
            echo -e "${RED}  Diff:${NC}"
            diff "$ok_file" "$temp_out" | sed 's/^/    /' || true
        fi
    else
        exit_code=$?
        if [ $exit_code -eq 124 ]; then
            echo -e "${RED}FAIL (timeout after ${TIMEOUT}s)${NC}"
            FAILED=$((FAILED + 1))
            echo -e "${RED}  Test timed out - possible infinite loop${NC}"
            if [ -s "$temp_out" ]; then
                echo -e "${RED}  Partial output:${NC}"
                cat "$temp_out" | sed 's/^/    /'
            fi
        else
            echo -e "${RED}FAIL (execution error)${NC}"
            FAILED=$((FAILED + 1))
            echo -e "${RED}  Error output:${NC}"
            cat "$temp_out" | sed 's/^/    /'
        fi
    fi
    
    # Clean up temporary file
    rm -f "$temp_out"
done

echo "=================================="
echo -e "${YELLOW}Summary:${NC}"
echo -e "Total tests: $TOTAL"
echo -e "${GREEN}Passed: $PASSED${NC}"
echo -e "${RED}Failed: $FAILED${NC}"

if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}All tests passed! 🎉${NC}"
    exit 0
else
    echo -e "${RED}Some tests failed. 😞${NC}"
    exit 1
fi
