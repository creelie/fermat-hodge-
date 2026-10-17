// closure_graph.cpp -- the closure graph of Sect. III of the paper, in C++.
// Build: c++ -std=c++17 -O2 -o closure_graph_cpp closure_graph.cpp && ./closure_graph_cpp
#include <bitset>
#include <iostream>
#include <set>
#include <vector>
#include <algorithm>
using Set = std::bitset<8>;
enum { HC, F3, F2, F3p, L, M, V, AB };
static const char *NAME[8] = {"HC","F3","F2","F3p","L","M","V","AB"};
struct Rule { Set prem; int concl; };
static Set mk(std::initializer_list<int> xs) { Set s; for (int x : xs) s.set(x); return s; }
static const std::vector<Rule> RULES = {
    {mk({HC}),F3},{mk({F3}),HC},{mk({HC}),F2},{mk({HC}),F3p},{mk({HC}),AB},{mk({F2}),AB},
    {mk({AB}),F2},{mk({AB,F3p}),HC},{mk({L,M}),HC},{mk({L}),AB},{mk({V}),AB},{mk({HC}),M}};
static Set closure(Set s) {
    for (;;) { Set n = s; for (auto &r : RULES) if ((r.prem & s) == r.prem) n.set(r.concl); if (n == s) return s; s = n; }
}
int main() {
    std::vector<bool> derive(256); int nd = 0;
    for (unsigned m = 0; m < 256; ++m) { derive[m] = closure(Set(m))[HC]; nd += derive[m]; }
    std::vector<unsigned> minimal;
    for (unsigned m = 0; m < 256; ++m) {
        if (Set(m)[HC] || !derive[m]) continue;
        bool min = true;
        for (unsigned t = 0; t < 256; ++t) if (t != m && (t & m) == t && !Set(t)[HC] && derive[t]) min = false;
        if (min) minimal.push_back(m);
    }
    std::sort(minimal.begin(), minimal.end(), [](unsigned a, unsigned b){ return Set(a).count() != Set(b).count() ? Set(a).count() < Set(b).count() : a < b; });
    std::cout << "subsets: 256  deriving HC: " << nd << "\nminimal sufficient sets: " << minimal.size() << "\n";
    for (unsigned m : minimal) { std::cout << "  {"; bool first = true; for (int i = 0; i < 8; ++i) if (Set(m)[i]) { std::cout << (first ? "" : ",") << NAME[i]; first = false; } std::cout << "}\n"; }
    std::set<unsigned long> expected = {mk({F3}).to_ulong(), mk({L,M}).to_ulong(), mk({L,F3p}).to_ulong(), mk({V,F3p}).to_ulong(), mk({F2,F3p}).to_ulong(), mk({AB,F3p}).to_ulong()};
    bool ok = std::set<unsigned long>(minimal.begin(), minimal.end()) == expected;
    for (Set s : {mk({F2}), mk({F3p}), mk({L}), mk({M}), mk({V}), mk({AB}), mk({L,V}), mk({M,F3p})}) if (derive[s.to_ulong()]) ok = false;
    std::cout << "closure_graph.cpp: " << (ok ? "PASS" : "FAIL") << "\n";
    return ok ? 0 : 1;
}
