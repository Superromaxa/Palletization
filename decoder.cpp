#include <algorithm>    // sort, max, min, unique
#include <chrono>       // timing
#include <cmath>        // fabs
#include <exception>    // exception, runtime_error
#include <fstream>      // ifstream, ofstream
#include <iomanip>      // setprecision, fixed
#include <iostream>     // cout, cerr
#include <random>       // mt19937, uniform distributions
#include <sstream>      // stringstream (если захочешь)
#include <stdexcept>    // runtime_error
#include <string>       // string, stoi, stod
#include <utility>      // pair
#include <vector>       // vector

using namespace std;

static constexpr double PALLET_L = 1200.0; // X
static constexpr double PALLET_W = 800.0;  // Y
static constexpr double MIN_SUPPORT = 0.60;
static constexpr double EPS = 1e-9;

// ------------------------ Data ------------------------

struct Box {
    int sku;
    double L, W, H;
    double weight;
    int aisle;
};

struct Placed {
    int sku;
    double x1,y1,z1,x2,y2,z2;
    int aisle;
    double weight;
    double baseL, baseW; // orientation used (dx,dy) for convenience
    bool on_ground;      // z1==0
};

static inline double area2d(double a, double b) { return a*b; }

// rotate only L<->W
struct OrientedDims {
    double dx, dy, dz;
    bool swapped;
};

static inline OrientedDims orientLW(const Box& b, bool swapLW){
    if(!swapLW) return {b.L, b.W, b.H, false};
    return {b.W, b.L, b.H, true};
}

// Axis-aligned overlap in XY
static inline bool overlap_xy(double ax1,double ay1,double ax2,double ay2,
                              double bx1,double by1,double bx2,double by2){
    return !(ax2 <= bx1 + EPS || bx2 <= ax1 + EPS || ay2 <= by1 + EPS || by2 <= ay1 + EPS);
}

// Full 3D overlap (AABB)
static inline bool overlap_3d(const Placed& p, double x1,double y1,double z1,double x2,double y2,double z2){
    bool sep =
        (x2 <= p.x1 + EPS) || (p.x2 <= x1 + EPS) ||
        (y2 <= p.y1 + EPS) || (p.y2 <= y1 + EPS) ||
        (z2 <= p.z1 + EPS) || (p.z2 <= z1 + EPS);
    return !sep;
}

// ------------------------ Convex hull for ground support (CoM) ------------------------

struct Pt { double x,y; };

static inline double cross(const Pt& a, const Pt& b, const Pt& c){
    return (b.x-a.x)*(c.y-a.y) - (b.y-a.y)*(c.x-a.x);
}

static vector<Pt> convex_hull(vector<Pt> pts){
    sort(pts.begin(), pts.end(), [](const Pt& a, const Pt& b){
        if (a.x != b.x) return a.x < b.x;
        return a.y < b.y;
    });
    pts.erase(unique(pts.begin(), pts.end(), [](const Pt& a, const Pt& b){
        return fabs(a.x-b.x)<1e-9 && fabs(a.y-b.y)<1e-9;
    }), pts.end());

    if (pts.size() <= 2) return pts;

    vector<Pt> lo, up;
    for (auto &p: pts){
        while (lo.size() >= 2 && cross(lo[lo.size()-2], lo.back(), p) <= 0) lo.pop_back();
        lo.push_back(p);
    }
    for (int i=(int)pts.size()-1; i>=0; --i){
        auto p = pts[i];
        while (up.size() >= 2 && cross(up[up.size()-2], up.back(), p) <= 0) up.pop_back();
        up.push_back(p);
    }
    lo.pop_back();
    up.pop_back();
    lo.insert(lo.end(), up.begin(), up.end());
    return lo;
}

static bool point_in_convex_polygon(const vector<Pt>& poly, Pt p){
    if (poly.empty()) return false;
    if (poly.size()==1) return (fabs(poly[0].x-p.x)<1e-9 && fabs(poly[0].y-p.y)<1e-9);
    if (poly.size()==2){
        // on segment (loose)
        double minx=min(poly[0].x,poly[1].x)-1e-9, maxx=max(poly[0].x,poly[1].x)+1e-9;
        double miny=min(poly[0].y,poly[1].y)-1e-9, maxy=max(poly[0].y,poly[1].y)+1e-9;
        return (p.x>=minx && p.x<=maxx && p.y>=miny && p.y<=maxy);
    }
    // All cross products should have same sign for convex polygon in CCW
    int n = (int)poly.size();
    double prev = 0;
    for(int i=0;i<n;i++){
        Pt a=poly[i], b=poly[(i+1)%n];
        double cr = (b.x-a.x)*(p.y-a.y) - (b.y-a.y)*(p.x-a.x);
        if (fabs(cr) < 1e-12) continue;
        if (prev==0) prev = cr;
        else if ((prev>0) != (cr>0)) return false;
    }
    return true;
}

// ------------------------ Packing State ------------------------

struct State {
    vector<Placed> placed;

    double total_weight = 0.0;
    double sum_wx = 0.0, sum_wy = 0.0; // for CoM in XY
    double total_volume = 0.0;
    double max_z = 0.0;

    // ground support polygon cache
    vector<Pt> ground_hull;
    bool hull_dirty = true;

    void addPlaced(const Placed& p){
        placed.push_back(p);
        total_weight += p.weight;
        double cx = 0.5*(p.x1+p.x2);
        double cy = 0.5*(p.y1+p.y2);
        sum_wx += p.weight * cx;
        sum_wy += p.weight * cy;
        total_volume += (p.x2-p.x1)*(p.y2-p.y1)*(p.z2-p.z1);
        max_z = max(max_z, p.z2);
        if (p.on_ground) hull_dirty = true;
    }

    Pt center_of_mass_xy() const {
        if (total_weight <= 0) return {PALLET_L/2.0, PALLET_W/2.0};
        return {sum_wx/total_weight, sum_wy/total_weight};
    }

    void rebuild_ground_hull_if_needed(){
        if (!hull_dirty) return;
        vector<Pt> pts;
        pts.reserve(placed.size()*4);
        for (auto &p: placed){
            if (!p.on_ground) continue;
            pts.push_back({p.x1,p.y1});
            pts.push_back({p.x2,p.y1});
            pts.push_back({p.x2,p.y2});
            pts.push_back({p.x1,p.y2});
        }
        // If nothing on ground yet, treat whole pallet as support
        if (pts.empty()){
            ground_hull = {{0,0},{PALLET_L,0},{PALLET_L,PALLET_W},{0,PALLET_W}};
        } else {
            ground_hull = convex_hull(pts);
        }
        hull_dirty = false;
    }
};

// ------------------------ Core geometry for "drop" and support ------------------------

// compute minimal z where box (x,y,dx,dy) can sit without intersecting existing boxes
static double compute_drop_z(const State& st, double x, double y, double dx, double dy){
    double z = 0.0;
    for (const auto& p: st.placed){
        if (!overlap_xy(x,y,x+dx,y+dy, p.x1,p.y1,p.x2,p.y2)) continue;
        // to avoid overlap in 3D, we must be above p.z2
        z = max(z, p.z2);
    }
    return z;
}

static bool check_no_overlap_at(const State& st, double x,double y,double z,double dx,double dy,double dz){
    double x2=x+dx, y2=y+dy, z2=z+dz;
    for (const auto& p: st.placed){
        if (overlap_3d(p, x,y,z, x2,y2,z2)) return false;
    }
    return true;
}

// support ratio: area overlap of base with top faces exactly at height z
static double support_ratio(const State& st, double x,double y,double z,double dx,double dy){
    if (z <= EPS) return 1.0;
    double baseA = dx*dy;
    if (baseA <= 0) return 0.0;
    double supA = 0.0;

    for (const auto& p: st.placed){
        if (fabs(p.z2 - z) > 1e-6) continue; // must touch exactly at that level
        // overlap in XY of base with p top face rectangle
        double ox1 = max(x, p.x1);
        double oy1 = max(y, p.y1);
        double ox2 = min(x+dx, p.x2);
        double oy2 = min(y+dy, p.y2);
        double w = ox2 - ox1;
        double h = oy2 - oy1;
        if (w > 0 && h > 0) supA += w*h;
    }
    return supA / baseA;
}

// ------------------------ Candidate generation ------------------------

// Deterministic candidates: take x from {0, x1, x2} of placed, same for y.
// This is “extreme points-like” but cheap and robust.
static vector<pair<double,double>> generate_xy_candidates_for_dims(const State& st, double dx, double dy){
    vector<pair<double,double>> out;
    out.reserve(st.placed.size()*12 + 10);

    auto push = [&](double x, double y){
        // clamp so that box fits into pallet
        x = min(max(0.0, x), PALLET_L - dx);
        y = min(max(0.0, y), PALLET_W - dy);
        out.push_back({x,y});
    };

    // pallet corners / edges
    push(0,0);
    push(PALLET_L - dx, 0);
    push(0, PALLET_W - dy);
    push(PALLET_L - dx, PALLET_W - dy);

    for (const auto& p : st.placed){
        // classic extreme/corner points
        push(p.x1, p.y1);
        push(p.x1, p.y2);
        push(p.x2, p.y1);
        push(p.x2, p.y2);

        // IMPORTANT: "snap by size" so we can fill gaps tightly
        push(p.x1 - dx, p.y1);
        push(p.x1 - dx, p.y2);
        push(p.x2 - dx, p.y1);
        push(p.x2 - dx, p.y2);

        push(p.x1, p.y1 - dy);
        push(p.x2, p.y1 - dy);
        push(p.x1, p.y2 - dy);
        push(p.x2, p.y2 - dy);

        // edges
        push(p.x1, 0.0);
        push(p.x2 - dx, 0.0);
        push(0.0, p.y1);
        push(0.0, p.y2 - dy);
        push(PALLET_L - dx, p.y1);
        push(PALLET_L - dx, p.y2 - dy);
        push(p.x1, PALLET_W - dy);
        push(p.x2 - dx, PALLET_W - dy);
    }

    sort(out.begin(), out.end(), [](auto& a, auto& b){
        // prefer low y then low x (pack from one corner)
        if (a.second != b.second) return a.second < b.second;
        return a.first < b.first;
    });

    out.erase(unique(out.begin(), out.end(), [](auto& a, auto& b){
        return fabs(a.first-b.first)<1e-6 && fabs(a.second-b.second)<1e-6;
    }), out.end());

    return out;
}

static vector<double> generate_z_levels(const State& st, double drop_z){
    vector<double> levels;
    levels.reserve(st.placed.size() + 2);
    levels.push_back(0.0);

    for (const auto& p : st.placed) levels.push_back(p.z2);

    sort(levels.begin(), levels.end());
    levels.erase(unique(levels.begin(), levels.end(), [](double a, double b){
        return fabs(a-b) < 1e-6;
    }), levels.end());

    // Always try the computed drop_z as a fallback (may not be present due to eps)
    levels.push_back(drop_z);
    sort(levels.begin(), levels.end());
    levels.erase(unique(levels.begin(), levels.end(), [](double a, double b){
        return fabs(a-b) < 1e-6;
    }), levels.end());

    // IMPORTANT: cap number of levels to keep it fast
    // We keep the lowest levels (best for height), and also ensure drop_z included.
    const int CAP = 80; // tune 40..120
    if ((int)levels.size() > CAP){
        // keep first CAP-1 + last (which will be >= drop_z typically)
        vector<double> cut;
        cut.reserve(CAP);
        for(int i=0;i<CAP-1;i++) cut.push_back(levels[i]);
        cut.push_back(levels.back());
        levels.swap(cut);
        sort(levels.begin(), levels.end());
        levels.erase(unique(levels.begin(), levels.end(), [](double a, double b){
            return fabs(a-b) < 1e-6;
        }), levels.end());
    }

    return levels;
}




// Random candidates fallback
static vector<pair<double,double>> generate_random_xy(int count, std::mt19937& rng){
    std::uniform_real_distribution<double> dx(0.0, PALLET_L);
    std::uniform_real_distribution<double> dy(0.0, PALLET_W);
    vector<pair<double,double>> out;
    out.reserve(count);
    for(int i=0;i<count;i++) out.push_back({dx(rng), dy(rng)});
    return out;
}

// ------------------------ Scoring ------------------------

static inline double percolation(const State& st){
    double H = max(st.max_z, 1e-9);
    return st.total_volume / (PALLET_L * PALLET_W * H);
}

// Score candidate placement: prefer smaller resulting height, then higher percolation, then lower y,x
static double score_candidate(const State& st, double new_max_z){
    // bigger is better
    // strong weight on minimizing height:
    return -1e6 * new_max_z + 1e3 * percolation(st);
}

// ------------------------ Place one box ------------------------

struct BestMove {
    bool ok=false;
    bool swapLW=false;
    double x=0,y=0,z=0;
    double dx=0,dy=0,dz=0;
    double bestScore=-1e100;
};

static BestMove find_best_move_for_box(const State& st, const Box& b, std::mt19937& rng){
    BestMove best;

    auto consider_candidate = [&](bool sw, double x, double y, double z, double dx, double dy, double dz){
        if (x < -1e-9 || y < -1e-9) return;
        if (x + dx > PALLET_L + 1e-9) return;
        if (y + dy > PALLET_W + 1e-9) return;
        if (!check_no_overlap_at(st, x,y,z, dx,dy,dz)) return;
        if (support_ratio(st, x,y,z, dx,dy) + 1e-12 < MIN_SUPPORT) return;

        // CoM after placement must be inside hull of ground boxes
        State tmp = st;
        Placed p;
        p.sku=b.sku; p.aisle=b.aisle; p.weight=b.weight;
        p.x1=x; p.y1=y; p.z1=z;
        p.x2=x+dx; p.y2=y+dy; p.z2=z+dz;
        p.baseL=dx; p.baseW=dy;
        p.on_ground = (z <= EPS);
        tmp.addPlaced(p);
        tmp.rebuild_ground_hull_if_needed();
        Pt cm = tmp.center_of_mass_xy();
        if (!point_in_convex_polygon(tmp.ground_hull, cm)) return;

        // Scoring: prioritize LOWER placement height (z), then lower overall height, then higher support
        double new_max_z = tmp.max_z;
        double sr = support_ratio(st, x,y,z, dx,dy);

        // lexicographic packed into one score
        // huge weight on z and new_max_z to suppress tower growth
        double sc = -1e9 * z - 1e6 * new_max_z + 1e3 * sr;

        // tie-break: closer to (0,0)
        sc -= 1e-3 * (x*x + y*y);

        if (!best.ok || sc > best.bestScore){
            best.ok = true;
            best.bestScore = sc;
            best.swapLW = sw;
            best.x=x; best.y=y; best.z=z;
            best.dx=dx; best.dy=dy; best.dz=dz;
        }
    };

    // Try two orientations: (L,W) and (W,L)
    for (int ori=0; ori<2; ++ori){
        bool sw = (ori==1);
        auto d = orientLW(b, sw);
        double dx=d.dx, dy=d.dy, dz=d.dz;
        if (dx > PALLET_L + EPS || dy > PALLET_W + EPS) continue;

        // XY candidates depend on dx,dy
        auto xys = generate_xy_candidates_for_dims(st, dx, dy);

        // For each XY, compute drop_z and then try shelves in increasing order
        for (auto [x,y] : xys){
            double drop = compute_drop_z(st, x,y,dx,dy);
            auto levels = generate_z_levels(st, drop);

            // Try lowest shelves first; usually we break early if z exceeds current best too much
            for (double z : levels){
                // quick pruning: if we already have a best and z is much higher than best.z, skip
                if (best.ok && z > best.z + 1e-6) {
                    // still allow if z is same but maybe improves other metrics – but main win is low z
                    // keep small slack:
                    if (z > best.z + 50.0) break; // 50 mm slack; tune
                }
                consider_candidate(sw, x,y,z, dx,dy,dz);
                // If we found something at z=0, it's hard to beat by height; continue a bit but can early stop
                if (best.ok && best.z <= EPS) break;
            }
        }

        // Random fallback only if nothing found in deterministic
        if (!best.ok){
            std::uniform_real_distribution<double> rx(0.0, PALLET_L - dx);
            std::uniform_real_distribution<double> ry(0.0, PALLET_W - dy);
            for(int t=0; t<6000; ++t){
                double x = rx(rng), y = ry(rng);
                double drop = compute_drop_z(st, x,y,dx,dy);
                auto levels = generate_z_levels(st, drop);
                for (double z: levels){
                    consider_candidate(sw, x,y,z, dx,dy,dz);
                    if (best.ok && best.z <= EPS) break;
                }
            }
        }
    }

    return best;
}


// ------------------------ CSV parsing ------------------------

static inline string trim(const string& s){
    size_t i=0, j=s.size();
    while(i<j && isspace((unsigned char)s[i])) i++;
    while(j>i && isspace((unsigned char)s[j-1])) j--;
    return s.substr(i, j-i);
}

static vector<string> split_csv_line(const string& line){
    // simple split by comma (your data seems not quoted)
    vector<string> out;
    string cur;
    for(char c: line){
        if (c==','){
            out.push_back(trim(cur));
            cur.clear();
        } else cur.push_back(c);
    }
    out.push_back(trim(cur));
    return out;
}

static vector<Box> read_boxes_with_quantity(const string& path){
    ifstream fin(path);
    if(!fin) throw runtime_error("Cannot open input " + path);

    string line;
    // Read first non-empty line(s)
    while (std::getline(fin, line)){
        line = trim(line);
        if (!line.empty()) break;
    }
    if (line.empty()) return {};

    // If first line is not header, skip until header
    if (line.rfind("SKU", 0) != 0){
        // skip this line (like 1111141001011149550)
        while (std::getline(fin, line)){
            line = trim(line);
            if (line.rfind("SKU", 0) == 0) break;
        }
    }

    // Now line should be header
    // Read data
    vector<Box> boxes;
    while (std::getline(fin, line)){
        line = trim(line);
        if (line.empty()) continue;
        auto cols = split_csv_line(line);
        // Expect at least 9 columns
        if (cols.size() < 9) continue;

        int sku = stoi(cols[0]);
        int qty = stoi(cols[1]);
        double L = stod(cols[2]);
        double W = stod(cols[3]);
        double H = stod(cols[4]);
        double weight = stod(cols[5]);
        // strength cols[6] ignored
        int aisle = stoi(cols[7]);
        // caustic cols[8] ignored

        for(int i=0;i<qty;i++){
            boxes.push_back(Box{sku, L, W, H, weight, aisle});
        }
    }
    return boxes;
}

// ------------------------ Main packing ------------------------

static State pack_all_boxes(vector<Box> boxes, unsigned seed=1){
    // sort by base area descending (try both orientations and take max base area for sorting)
    sort(boxes.begin(), boxes.end(), [](const Box& a, const Box& b){
        double a1 = area2d(a.L,a.W);
        double b1 = area2d(b.L,b.W);
        if (a1 != b1) return a1 > b1;
        // tie-break: heavier first (stability/CoM)
        if (a.weight != b.weight) return a.weight > b.weight;
        return a.H > b.H;
    });

    std::mt19937 rng(seed);

    State st;
    // Start with "virtual ground hull" = full pallet (handled in rebuild)
    st.rebuild_ground_hull_if_needed();

    for (size_t i=0;i<boxes.size();++i){
        const Box& b = boxes[i];
        auto mv = find_best_move_for_box(st, b, rng);
        if (!mv.ok){
            // As a last resort, increase random tries a lot (still bounded)
            bool placed=false;
            for(int extra=0; extra<5 && !placed; ++extra){
                auto mv2 = find_best_move_for_box(st, b, rng);
                if (mv2.ok){ mv = mv2; placed=true; }
            }
            if (!mv.ok){
                // If this happens, it means constraints + candidate generation didn’t find a feasible spot.
                // You said “all fit”, so we treat it as algorithmic failure.
                cerr << "[FAIL] Could not place box sku=" << b.sku
                     << " (index " << i << " of " << boxes.size() << ")\n";
                throw runtime_error("Packing failed under stability/CoM constraints.");
            }
        }

        Placed p;
        p.sku=b.sku; p.aisle=b.aisle; p.weight=b.weight;
        p.x1=mv.x; p.y1=mv.y; p.z1=mv.z;
        p.x2=mv.x+mv.dx; p.y2=mv.y+mv.dy; p.z2=mv.z+mv.dz;
        p.baseL=mv.dx; p.baseW=mv.dy;
        p.on_ground = (mv.z <= EPS);

        st.addPlaced(p);
        st.rebuild_ground_hull_if_needed();
    }

    return st;
}

static void write_output_csv(const string& path, const State& st){
    ofstream fout(path);
    if(!fout) throw runtime_error("Cannot open output " + path);

    double H_total = st.max_z;
    double perc = percolation(st);
    double W_total = st.total_weight;

    fout.setf(std::ios::fixed); fout<<setprecision(6);
    fout << H_total << " " << perc << " " << W_total << "\n";
    fout << "SKU_i,x_1^i,y_1^i,z_1^i,x_2^i,y_2^i,z_2^i,Aisle,Weight\n";
    for (const auto& p: st.placed){
        fout << p.sku << ","
             << p.x1 << "," << p.y1 << "," << p.z1 << ","
             << p.x2 << "," << p.y2 << "," << p.z2 << ","
             << p.aisle << "," << p.weight << ",\n";
    }
}

// ------------------------ Example main ------------------------

int main(){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    try{
        for (int k=2; k<17; ++k){
            string in_file  = "order_" + to_string(k) + ".csv";
            string out_file = "order_" + to_string(k) + "_out_stable3d.csv";

            auto t0 = chrono::high_resolution_clock::now();

            auto boxes = read_boxes_with_quantity(in_file);
            State st = pack_all_boxes(boxes, /*seed=*/(unsigned)k);

            auto t1 = chrono::high_resolution_clock::now();
            double ms = chrono::duration<double, std::milli>(t1-t0).count();

            write_output_csv(out_file, st);

            cerr << "[k="<<k<<"] boxes="<<boxes.size()
                 << " height="<<st.max_z
                 << " percolation="<<percolation(st)
                 << " time_ms="<<ms << "\n";
        }
    } catch(const exception& e){
        cerr << "ERROR: " << e.what() << "\n";
        return 1;
    }
    return 0;
}
