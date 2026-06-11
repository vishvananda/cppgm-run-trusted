#pragma once

#include <cstdint>
#include <map>
#include <string>
#include <vector>

using namespace std;

namespace cy86 {

struct ExternalRelocation
{
	size_t section;
	uint64_t offset;
	uint32_t type;
	size_t symbol;
	int64_t addend;
};

struct ExternalSymbol
{
	string name;
	size_t section;
	uint64_t value;
	bool defined;
	bool global;
	bool function;
};

struct ExternalSection
{
	string name;
	vector<unsigned char> data;
	uint64_t size;
	uint64_t align;
	bool alloc;
	bool executable;
	bool writable;
	bool nobits;
	uint64_t address;
};

struct ExternalObject
{
	vector<ExternalSection> sections;
	vector<ExternalSymbol> symbols;
	vector<ExternalRelocation> relocations;
};

ExternalObject load_elf64_relocatable(const string& path);

}  // namespace cy86
