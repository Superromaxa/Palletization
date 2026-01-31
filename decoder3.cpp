#include <algorithm>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

static constexpr double PALLET_L = 1200.0;
static constexpr double PALLET_W = 800.0;
static constexpr double MIN_SUPPORT = 0.60;
static constexpr double EPS = 1e-9;

struct Box {
    int sku = 0;
    double L = 0.0;
    double W = 0.0;
    double H = 0.0;
    double weight = 0.0;
    int aisle = 0;
};

struct Placed {
    int sku = 0;
    double x1 = 0.0;
    double y1 = 0.0;
    double z1 = 0.0;
    double x2 = 0.0;
    double y2 = 0.0;
    double z2 = 0.0;
    int aisle = 0;
    double weight = 0.0;
};

struct Rect {
    double x1 = 0.0;
    double y1 = 0.0;
    double x2 = 0.0;
    double y2 = 0.0;
};

struct Pt {
    double x = 0.0;
    double y = 0.0;
};

static inline bool overlap_xy(double ax1, double ay1, double ax2, double ay2,
                              double bx1, double by1, double bx2, double by2) {
    return !(ax2 <= bx1 + EPS || bx2 <= ax1 + EPS || ay2 <= by1 + EPS || by2 <= ay1 + EPS);
}

static inline bool overlap_3d(const Placed &p, double x1, double y1, double z1, double x2, double y2, double z2) {
    bool separated = (x2 <= p.x1 + EPS) || (p.x2 <= x1 + EPS) ||
                     (y2 <= p.y1 + EPS) || (p.y2 <= y1 + EPS) ||
                     (z2 <= p.z1 + EPS) || (p.z2 <= z1 + EPS);
    return !separated;
}

static inline double clamp(double v, double lo, double hi) {
    return max(lo, min(v, hi));
}

static double cross(const Pt &a, const Pt &b, const Pt &c) {
    return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
}

static vector<Pt> convex_hull(vector<Pt> pts) {
    sort(pts.begin(), pts.end(), [](const Pt &a, const Pt &b) {
        if (a.x != b.x) return a.x < b.x;
        return a.y < b.y;
    });
    pts.erase(unique(pts.begin(), pts.end(), [](const Pt &a, const Pt &b) {
        return fabs(a.x - b.x) < 1e-9 && fabs(a.y - b.y) < 1e-9;
    }), pts.end());

    if (pts.size() <= 2) return pts;

    vector<Pt> lower;
    vector<Pt> upper;
    for (const auto &p : pts) {
        while (lower.size() >= 2 && cross(lower[lower.size() - 2], lower.back(), p) <= 0.0) {
            lower.pop_back();
        }
        lower.push_back(p);
    }
    for (int i = static_cast<int>(pts.size()) - 1; i >= 0; --i) {
        const auto &p = pts[i];
        while (upper.size() >= 2 && cross(upper[upper.size() - 2], upper.back(), p) <= 0.0) {
            upper.pop_back();
        }
        upper.push_back(p);
    }
    lower.pop_back();
    upper.pop_back();
    lower.insert(lower.end(), upper.begin(), upper.end());
    return lower;
}

static bool point_in_convex_polygon(const vector<Pt> &poly, const Pt &p) {
    if (poly.empty()) return false;
    if (poly.size() == 1) {
        return fabs(poly[0].x - p.x) < 1e-9 && fabs(poly[0].y - p.y) < 1e-9;
    }
    if (poly.size() == 2) {
        double minx = min(poly[0].x, poly[1].x) - 1e-9;
        double maxx = max(poly[0].x, poly[1].x) + 1e-9;
        double miny = min(poly[0].y, poly[1].y) - 1e-9;
        double maxy = max(poly[0].y, poly[1].y) + 1e-9;
        return p.x >= minx && p.x <= maxx && p.y >= miny && p.y <= maxy;
    }
    double prev = 0.0;
    for (size_t i = 0; i < poly.size(); ++i) {
        const auto &a = poly[i];
        const auto &b = poly[(i + 1) % poly.size()];
        double cr = (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x);
        if (fabs(cr) < 1e-12) continue;
        if (prev == 0.0) prev = cr;
        else if ((prev > 0.0) != (cr > 0.0)) return false;
    }
    return true;
}

static inline string trim(const string &s) {
    size_t i = 0, j = s.size();
    while (i < j && isspace(static_cast<unsigned char>(s[i]))) ++i;
    while (j > i && isspace(static_cast<unsigned char>(s[j - 1]))) --j;
    return s.substr(i, j - i);
}

static vector<string> split_csv_line(const string &line) {
    vector<string> out;
    string cur;
    for (char c : line) {
        if (c == ',') {
            out.push_back(trim(cur));
            cur.clear();
        } else {
            cur.push_back(c);
        }
    }
    out.push_back(trim(cur));
    return out;
}

static vector<Box> read_boxes(const string &path) {
    ifstream fin(path);
    if (!fin) {
        throw runtime_error("Cannot open input file: " + path);
    }

    string line;
    while (getline(fin, line)) {
        line = trim(line);
        if (!line.empty()) break;
    }
    if (line.empty()) return {};

    if (line.rfind("SKU", 0) != 0) {
        while (getline(fin, line)) {
            line = trim(line);
            if (line.rfind("SKU", 0) == 0) break;
        }
    }

    vector<Box> boxes;
    while (getline(fin, line)) {
        line = trim(line);
        if (line.empty()) continue;
        auto cols = split_csv_line(line);
        if (cols.size() < 9) continue;

        int sku = stoi(cols[0]);
        int qty = stoi(cols[1]);
        double L = stod(cols[2]);
        double W = stod(cols[3]);
        double H = stod(cols[4]);
        double weight = stod(cols[5]);
        int aisle = stoi(cols[7]);

        for (int i = 0; i < qty; ++i) {
            boxes.push_back(Box{sku, L, W, H, weight, aisle});
        }
    }
    return boxes;
}

struct State {
    vector<Placed> placed;
    double total_weight = 0.0;
    double sum_wx = 0.0;
    double sum_wy = 0.0;
    double total_volume = 0.0;
    double max_z = 0.0;
    vector<Rect> ground_boxes;
    vector<Pt> ground_hull;
    bool hull_dirty = true;

    void add(const Placed &p) {
        placed.push_back(p);
        total_weight += p.weight;
        double cx = 0.5 * (p.x1 + p.x2);
        double cy = 0.5 * (p.y1 + p.y2);
        sum_wx += p.weight * cx;
        sum_wy += p.weight * cy;
        total_volume += (p.x2 - p.x1) * (p.y2 - p.y1) * (p.z2 - p.z1);
        max_z = max(max_z, p.z2);
        if (p.z1 <= EPS) {
            ground_boxes.push_back({p.x1, p.y1, p.x2, p.y2});
            hull_dirty = true;
        }
    }

    pair<double, double> center_of_mass() const {
        if (total_weight <= 0.0) return {PALLET_L / 2.0, PALLET_W / 2.0};
        return {sum_wx / total_weight, sum_wy / total_weight};
    }

    void rebuild_ground_hull_if_needed() {
        if (!hull_dirty) return;
        vector<Pt> pts;
        pts.reserve(ground_boxes.size() * 4);
        for (const auto &r : ground_boxes) {
            pts.push_back({r.x1, r.y1});
            pts.push_back({r.x2, r.y1});
            pts.push_back({r.x2, r.y2});
            pts.push_back({r.x1, r.y2});
        }
        if (pts.empty()) {
            ground_hull = {{0.0, 0.0}, {PALLET_L, 0.0}, {PALLET_L, PALLET_W}, {0.0, PALLET_W}};
        } else {
            ground_hull = convex_hull(move(pts));
        }
        hull_dirty = false;
    }
};

static double compute_drop_z(const State &st, double x, double y, double dx, double dy) {
    double z = 0.0;
    for (const auto &p : st.placed) {
        if (!overlap_xy(x, y, x + dx, y + dy, p.x1, p.y1, p.x2, p.y2)) continue;
        z = max(z, p.z2);
    }
    return z;
}

static vector<double> generate_z_candidates(const State &st, double x, double y, double dx, double dy, double drop_z) {
    vector<double> levels;
    levels.reserve(st.placed.size() + 2);
    levels.push_back(0.0);
    levels.push_back(drop_z);

    for (const auto &p : st.placed) {
        if (p.z2 + 1e-6 < drop_z) continue;
        if (!overlap_xy(x, y, x + dx, y + dy, p.x1, p.y1, p.x2, p.y2)) continue;
        levels.push_back(p.z2);
    }

    sort(levels.begin(), levels.end());
    levels.erase(unique(levels.begin(), levels.end(), [](double a, double b) {
        return fabs(a - b) < 1e-6;
    }), levels.end());

    const size_t cap = 60;
    if (levels.size() > cap) {
        vector<double> cut;
        cut.reserve(cap);
        for (size_t i = 0; i < cap / 2; ++i) cut.push_back(levels[i]);
        for (size_t i = levels.size() - cap / 2; i < levels.size(); ++i) cut.push_back(levels[i]);
        levels.swap(cut);
        sort(levels.begin(), levels.end());
        levels.erase(unique(levels.begin(), levels.end(), [](double a, double b) {
            return fabs(a - b) < 1e-6;
        }), levels.end());
    }

    return levels;
}

static bool check_no_overlap_at(const State &st, double x, double y, double z, double dx, double dy, double dz) {
    double x2 = x + dx;
    double y2 = y + dy;
    double z2 = z + dz;
    for (const auto &p : st.placed) {
        if (overlap_3d(p, x, y, z, x2, y2, z2)) return false;
    }
    return true;
}

static double support_ratio(const State &st, double x, double y, double z, double dx, double dy) {
    if (z <= EPS) return 1.0;
    double baseA = dx * dy;
    if (baseA <= 0.0) return 0.0;
    double supportA = 0.0;

    for (const auto &p : st.placed) {
        if (fabs(p.z2 - z) > 1e-6) continue;
        double ox1 = max(x, p.x1);
        double oy1 = max(y, p.y1);
        double ox2 = min(x + dx, p.x2);
        double oy2 = min(y + dy, p.y2);
        double w = ox2 - ox1;
        double h = oy2 - oy1;
        if (w > 0.0 && h > 0.0) supportA += w * h;
    }
    return supportA / baseA;
}

static bool center_of_mass_supported(const State &st, const Placed &candidate) {
    State tmp = st;
    tmp.add(candidate);
    auto [cx, cy] = tmp.center_of_mass();
    tmp.rebuild_ground_hull_if_needed();
    if (tmp.ground_hull.empty()) return true;
    return point_in_convex_polygon(tmp.ground_hull, {cx, cy});
}

struct Candidate {
    bool ok = false;
    double x = 0.0;
    double y = 0.0;
    double z = 0.0;
    double dx = 0.0;
    double dy = 0.0;
    double dz = 0.0;
    double score = -1e100;
    bool swapped = false;
};

static vector<pair<double, double>> generate_xy_candidates(const State &st, double dx, double dy) {
    vector<pair<double, double>> points;
    points.reserve(st.placed.size() * 8 + 4);

    auto push = [&](double x, double y) {
        x = clamp(x, 0.0, PALLET_L - dx);
        y = clamp(y, 0.0, PALLET_W - dy);
        points.emplace_back(x, y);
    };

    push(0.0, 0.0);
    push(PALLET_L - dx, 0.0);
    push(0.0, PALLET_W - dy);
    push(PALLET_L - dx, PALLET_W - dy);

    for (const auto &p : st.placed) {
        push(p.x1, p.y1);
        push(p.x2 - dx, p.y1);
        push(p.x1, p.y2 - dy);
        push(p.x2 - dx, p.y2 - dy);
        push(p.x1 - dx, p.y1);
        push(p.x1, p.y1 - dy);
        push(p.x2, p.y2);
        push(p.x2 - dx, p.y2 - dy);
    }

    sort(points.begin(), points.end(), [](const auto &a, const auto &b) {
        if (a.second != b.second) return a.second < b.second;
        return a.first < b.first;
    });

    points.erase(unique(points.begin(), points.end(), [](const auto &a, const auto &b) {
        return fabs(a.first - b.first) < 1e-6 && fabs(a.second - b.second) < 1e-6;
    }), points.end());

    return points;
}

static Candidate find_best_for_box(const State &st, const Box &b, mt19937 &rng) {
    Candidate best;

    auto consider = [&](bool swapped, double x, double y, double z, double dx, double dy, double dz) {
        if (x < -EPS || y < -EPS || x + dx > PALLET_L + EPS || y + dy > PALLET_W + EPS) return;
        if (!check_no_overlap_at(st, x, y, z, dx, dy, dz)) return;
        double sr = support_ratio(st, x, y, z, dx, dy);
        if (sr + 1e-12 < MIN_SUPPORT) return;

        Placed p{b.sku, x, y, z, x + dx, y + dy, z + dz, b.aisle, b.weight};
        if (!center_of_mass_supported(st, p)) return;

        double new_max_z = max(st.max_z, z + dz);
        double new_volume = st.total_volume + dx * dy * dz;
        double new_perc = new_volume / (PALLET_L * PALLET_W * max(new_max_z, 1e-9));
        double score = -1e6 * new_max_z - 1e3 * z + 250.0 * new_perc + 10.0 * sr;
        score -= 1e-4 * (x * x + y * y);

        if (!best.ok || score > best.score) {
            best.ok = true;
            best.x = x;
            best.y = y;
            best.z = z;
            best.dx = dx;
            best.dy = dy;
            best.dz = dz;
            best.score = score;
            best.swapped = swapped;
        }
    };

    for (int ori = 0; ori < 2; ++ori) {
        bool swapped = (ori == 1);
        double dx = swapped ? b.W : b.L;
        double dy = swapped ? b.L : b.W;
        double dz = b.H;
        if (dx > PALLET_L + EPS || dy > PALLET_W + EPS) continue;

        auto candidates = generate_xy_candidates(st, dx, dy);
        for (const auto &[x, y] : candidates) {
            double drop_z = compute_drop_z(st, x, y, dx, dy);
            auto z_levels = generate_z_candidates(st, x, y, dx, dy, drop_z);
            for (double z : z_levels) {
                if (z + EPS < drop_z) continue;
                consider(swapped, x, y, z, dx, dy, dz);
            }
        }
    }

    if (!best.ok) {
        uniform_real_distribution<double> rx(0.0, PALLET_L);
        uniform_real_distribution<double> ry(0.0, PALLET_W);
        for (int t = 0; t < 6000; ++t) {
            bool swapped = (t % 2 == 1);
            double dx = swapped ? b.W : b.L;
            double dy = swapped ? b.L : b.W;
            double dz = b.H;
            if (dx > PALLET_L + EPS || dy > PALLET_W + EPS) continue;
            double x = clamp(rx(rng), 0.0, PALLET_L - dx);
            double y = clamp(ry(rng), 0.0, PALLET_W - dy);
            double drop_z = compute_drop_z(st, x, y, dx, dy);
            auto z_levels = generate_z_candidates(st, x, y, dx, dy, drop_z);
            for (double z : z_levels) {
                if (z + EPS < drop_z) continue;
                consider(swapped, x, y, z, dx, dy, dz);
            }
        }
    }

    if (!best.ok) {
        auto consider_relaxed = [&](bool swapped, double x, double y, double z, double dx, double dy, double dz) {
            if (x < -EPS || y < -EPS || x + dx > PALLET_L + EPS || y + dy > PALLET_W + EPS) return;
            if (!check_no_overlap_at(st, x, y, z, dx, dy, dz)) return;
            double sr = support_ratio(st, x, y, z, dx, dy);
            if (sr + 1e-12 < 0.50) return;

            Placed p{b.sku, x, y, z, x + dx, y + dy, z + dz, b.aisle, b.weight};
            if (!center_of_mass_supported(st, p)) return;

            double new_max_z = max(st.max_z, z + dz);
            double new_volume = st.total_volume + dx * dy * dz;
            double new_perc = new_volume / (PALLET_L * PALLET_W * max(new_max_z, 1e-9));
            double score = -1e6 * new_max_z - 1e3 * z + 250.0 * new_perc + 10.0 * sr;
            score -= 1e-4 * (x * x + y * y);

            if (!best.ok || score > best.score) {
                best.ok = true;
                best.x = x;
                best.y = y;
                best.z = z;
                best.dx = dx;
                best.dy = dy;
                best.dz = dz;
                best.score = score;
                best.swapped = swapped;
            }
        };

        uniform_real_distribution<double> rx(0.0, PALLET_L);
        uniform_real_distribution<double> ry(0.0, PALLET_W);
        for (int t = 0; t < 6000; ++t) {
            bool swapped = (t % 2 == 1);
            double dx = swapped ? b.W : b.L;
            double dy = swapped ? b.L : b.W;
            double dz = b.H;
            if (dx > PALLET_L + EPS || dy > PALLET_W + EPS) continue;
            double x = clamp(rx(rng), 0.0, PALLET_L - dx);
            double y = clamp(ry(rng), 0.0, PALLET_W - dy);
            double drop_z = compute_drop_z(st, x, y, dx, dy);
            auto z_levels = generate_z_candidates(st, x, y, dx, dy, drop_z);
            for (double z : z_levels) {
                if (z + EPS < drop_z) continue;
                consider_relaxed(swapped, x, y, z, dx, dy, dz);
            }
        }
    }

    return best;
}

static State pack_boxes(vector<Box> boxes, unsigned seed = 1) {
    sort(boxes.begin(), boxes.end(), [](const Box &a, const Box &b) {
        double area_a = a.L * a.W;
        double area_b = b.L * b.W;
        if (area_a != area_b) return area_a > area_b;
        if (a.weight != b.weight) return a.weight > b.weight;
        return a.H > b.H;
    });

    mt19937 rng(seed);
    State st;

    if (boxes.empty()) return st;

    Box first = boxes.front();
    if ((first.L > PALLET_L + EPS || first.W > PALLET_W + EPS) &&
        (first.W <= PALLET_L + EPS && first.L <= PALLET_W + EPS)) {
        swap(first.L, first.W);
    }
    if (first.L > PALLET_L + EPS || first.W > PALLET_W + EPS) {
        throw runtime_error("First box does not fit on pallet.");
    }

    Placed p0{first.sku, 0.0, 0.0, 0.0, first.L, first.W, first.H, first.aisle, first.weight};
    st.add(p0);

    for (size_t i = 1; i < boxes.size(); ++i) {
        const Box &b = boxes[i];
        auto best = find_best_for_box(st, b, rng);
        if (!best.ok) {
            throw runtime_error("Failed to place box sku=" + to_string(b.sku));
        }
        Placed p{b.sku, best.x, best.y, best.z, best.x + best.dx, best.y + best.dy, best.z + best.dz, b.aisle, b.weight};
        st.add(p);
    }

    return st;
}

static double percolation(const State &st) {
    double H = max(st.max_z, 1e-9);
    return st.total_volume / (PALLET_L * PALLET_W * H);
}

static void write_output(const string &path, const State &st) {
    ofstream fout(path);
    if (!fout) {
        throw runtime_error("Cannot open output file: " + path);
    }

    fout.setf(ios::fixed);
    fout << setprecision(6);
    fout << 1 << "\n";
    fout << st.max_z << " " << percolation(st) << " " << st.total_weight << "\n";
    fout << "SKU_i,x_1^i,y_1^i,z_1^i,x_2^i,y_2^i,z_2^i,Aisle,Weight\n";
    for (const auto &p : st.placed) {
        fout << p.sku << "," << p.x1 << "," << p.y1 << "," << p.z1 << ","
             << p.x2 << "," << p.y2 << "," << p.z2 << ","
             << p.aisle << "," << p.weight << ",\n";
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    using Clock = chrono::high_resolution_clock;

    for (int k = 2; k < 17; ++k) {
        string in_file = "order_" + to_string(k) + ".csv";
        string out_file = "order_" + to_string(k) + "_outc++.csv";

        try {
            auto t_start = Clock::now();

            auto boxes = read_boxes(in_file);
            State st = pack_boxes(boxes, 1U);
            write_output(out_file, st);

            auto t_end = Clock::now();
            chrono::duration<double, milli> elapsed = t_end - t_start;

            cerr << "[k=" << k << "] "
                 << "boxes=" << boxes.size()
                 << " height=" << st.max_z
                 << " percolation=" << fixed << setprecision(4) << percolation(st)
                 << " time_ms=" << elapsed.count()
                 << "\n";
        } catch (const exception &e) {
            cerr << "[k=" << k << "] ERROR: " << e.what() << "\n";
        }
    }

    return 0;
}
