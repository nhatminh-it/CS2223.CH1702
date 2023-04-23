#include <iostream>
#include <stdexcept>
#include <map>
#include <set>
#include <functional>
#include <string>
#include <vector>
#include <unordered_map>

#define ASSERT_MSG(cond, msg) { if (!(cond)) throw std::runtime_error("Assertion (" #cond ") failed at line " + std::to_string(__LINE__) + "! Msg '" + std::string(msg) + "'."); }
#define ASSERT(cond) ASSERT_MSG(cond, "")

using u8 = uint8_t;

size_t constexpr n = 3, m = 3;

class Board {
public:
    Board() : n_(n), m_(m), board_(n_ * m_) {}
    Board(std::string const & s) : n_(n), m_(m), board_(n_ * m_) {
        for (size_t i = 0; i < n_; ++i)
            for (size_t j = 0; j < m_; ++j)
                (*this)(i, j) = s.at(i * m_ + j) - '0';
    }
    u8 & operator () (size_t i, size_t j) { return board_[i * m_ + j]; }
    u8 const & operator () (size_t i, size_t j) const { return const_cast<Board&>(*this)(i, j); }
    bool operator == (Board const & o) const { return board_ == o.board_; }
    std::vector<Board> Neighbours() const {
        std::vector<Board> r;
        for (ptrdiff_t i = 0; i < n_; ++i)
            for (ptrdiff_t j = 0; j < m_; ++j)
                if ((*this)(i, j) == 0) {
                    for (std::pair<int, int> p: std::vector<std::pair<int, int>>{{0, -1}, {0, 1}, {-1, 0}, {1, 0}}) {
                        ptrdiff_t const ni = i + p.first, nj = j + p.second;
                        if (ni < 0 || ni >= n_ || nj < 0 || nj >= m_)
                            continue;
                        Board o = *this;
                        std::swap(o(i, j), o(ni, nj));
                        r.push_back(std::move(o));
                    }
                    break;
                }
        return std::move(r);
    }
    std::string Str(bool newline = false) const {
        std::string r;
        for (size_t i = 0; i < n_; ++i) {
            for (size_t j = 0; j < m_; ++j)
                r.append(1, (*this)(i, j) + '0');
            if (newline && i + 1 < n_)
                r.append(1, '\n');
        }
        return r;
    }
    size_t MinDist(Board const & to) const {
        size_t r = 0;
        for (ptrdiff_t i = 0; i < n_; ++i)
            for (ptrdiff_t j = 0; j < m_; ++j) {
                auto const v = (*this)(i, j);
                if (v == 0)
                    continue;
                size_t dist = size_t(-1);
                for (ptrdiff_t i2 = 0; i2 < n_; ++i2) {
                    for (ptrdiff_t j2 = 0; j2 < m_; ++j2)
                        if (to(i2, j2) == v) {
                            dist = std::abs(i - i2) + std::abs(j - j2);
                            break;
                        }
                    if (dist != size_t(-1))
                        break;
                }
                ASSERT(dist != -1);
                r += dist;
            }
        return r;
    }
private:
    size_t n_ = 0, m_ = 0;
    std::vector<u8> board_;
};

std::vector<Board> AStarSolve(Board const & start, Board const & goal) {
    // https://en.wikipedia.org/wiki/A*_search_algorithm#Pseudocode
    using IdT = std::string;
    struct Entry {
        Board board;
        size_t gscore = size_t(-1), fscore = size_t(-1);
        IdT came_from{};
    };
    std::unordered_map<IdT, Entry> entries;
    std::map<size_t, std::set<IdT>> open_set;
    
    auto H = [&](Entry const & e) {
        return e.board.MinDist(goal);
    };
    
    {
        Entry first{.board = start, .gscore = 0};
        first.fscore = H(first);
        entries[first.board.Str()] = first;
        open_set[first.fscore].insert(first.board.Str());
    }
    
    std::function<std::vector<Board>(IdT const &, size_t)> ReconstructPath =
        [&](IdT const & id, size_t depth){
            thread_local std::vector<Board> path;
            if (id == IdT{})
                return path;
            if (depth == 0)
                path.clear();
            auto const & e = entries.at(id);
            path.insert(path.begin(), e.board);
            return ReconstructPath(e.came_from, depth + 1);
        };
    
    while (!open_set.empty()) {
        auto const min_fscore = open_set.begin()->first;
        auto const min_entries = open_set.begin()->second;
        for (auto const & id: min_entries)
            if (entries.at(id).board == goal)
                return ReconstructPath(id, 0);
        open_set.erase(min_fscore);
        for (auto const & cid: min_entries) {
            auto const & cure = entries.at(cid);
            for (auto const & nbid: cure.board.Neighbours()) {
                size_t const tentative_gscore = cure.gscore + 1;
                auto const nid = nbid.Str();
                auto it = entries.find(nid);
                bool is_new = it == entries.end();
                if (is_new || tentative_gscore < it->second.gscore) {
                    if (is_new)
                        it = entries.insert({nid, Entry{.board = nbid}}).first;
                    it->second.came_from = cid;
                    it->second.gscore = tentative_gscore;
                    if (!is_new) {
                        auto it2 = open_set.find(it->second.fscore);
                        if (it2 != open_set.end() && it2->second.count(nid)) {
                            it2->second.erase(nid);
                            if (it2->second.empty())
                                open_set.erase(it2);
                        }
                    }
                    it->second.fscore = tentative_gscore + H(it->second);
                    open_set[it->second.fscore].insert(nid);
                }
            }
        }
    }
    ASSERT_MSG(false, "Unreachable!");
}

void Solve(std::string const & start, std::string const & goal) {
    auto const v = AStarSolve(start, goal);
    size_t constexpr per_line = 5;
    bool last = false;
    for (size_t i = 0; !last; ++i) {
        for (size_t j = 0; j < n; ++j) {
            for (size_t i2 = 0; i2 < per_line; ++i2) {
                size_t const k = i * per_line + i2;
                if (k >= v.size()) {
                    last = true;
                    for (size_t l = 0; l < (m + 5); ++l)
                        std::cout << " ";
                } else {
                    auto const & e = v.at(k);
                    auto const s = e.Str(true);
                    size_t pos = 0;
                    for (size_t ip = 0; ip < j; ++ip)
                        pos = s.find('\n', pos) + 1;
                    size_t pos2 = std::min<size_t>(s.size(), s.find('\n', pos));
                    std::cout << s.substr(pos, pos2 - pos) << (j == (n / 2) && k + 1 < v.size() ? " --> " : "     ");
                }
                std::cout << (i2 + 1 >= per_line ? "\n" : "");
            }
        }
        std::cout << std::endl;
    }
}

int main() {
    try {
        Solve("042158367", "123456780");
        return 0;
    } catch (std::exception const & ex) {
        std::cout << "Exception: " << ex.what() << std::endl;
        return -1;
    }
}
