#include <bits/stdc++.h>
#include <chrono>

using namespace std;
int SECONDS;

static unsigned int randSeed = 1;

int customRand() {
    randSeed = randSeed * 1103515245 + 12345;
    return (1LL * randSeed / 65536) % 32768;
}

struct pair_hash {
    std::size_t operator()(const std::pair<int, int> &v) const {
        return 1LL * (1LL * v.first + 1LL * v.second * 666013) % 1000000007;
    }
};

string output, s, outputFileName, inputFileName;
std::chrono::time_point<std::chrono::high_resolution_clock> begin_;
vector<pair<int, int>> edgesReduced;
unordered_set<pair<int, int>, pair_hash> edges;
vector<pair<pair<int, int>, int >> toBeErasedBypass;
vector<pair<int, int>> toBeErasedDOME, toBeErasedSCC;
vector<bool> availableNode, inStack, availableNodeReduced, visitedCORE;
vector<pair<pair<int, unordered_set<int>::iterator>, int> > stackTarjan;
int n, m, fitnessType, sccIndex, sccCounter, testNo, currentErased, firstTime, changed, ratioIndex;
vector<unordered_set<int>> inDegreeReducedSimple, degreeDouble, inDegreeSimple, outDegreeSimple, degreeReducedDouble, outDegreeReducedSimple;
vector<int> inNodes, outNodes, localDFVS, local, selfLoopNodes, zeroDegreeNodes, oneDegreeNodes, lowLevel, sccStack, currLevel, whichSCC, candidatesSorted;
unordered_set<int> candidatesSortedSet, candidatesNodesReduced, localSet, cliqueCORE, candidatesNodes, feedbackVertexSet, bestFeedbackVertexSet, lastFeedbackVertexSet, feedbackVertexSetReduced;
vector<long long> lastFitness;
vector<int> chunk = {3, 4, 5, 6, 7, 8, 9, 10}, toBeErasedSet;
unordered_set<int> cl2[2], cl3[3], ll, set1;

auto cmp = [](pair<long long, int> a, pair<long long, int> b) {
    return a.first > b.first || (a.first == b.first && a.second > b.second);
};
set<pair<long long, int>, decltype(cmp)> availableNodes(cmp);

void doBasicReductions();

void loop();

void findDFVS();

void readData();

void createInitialDFVS();

void improveFeedbackVertexSet();

void doLocalSearch();

void solveTestcase();

void checkTime();

void eraseEdge(int x, int y, int z);

void addEdge(int x, int y);

void initializeSets();

void clearSets();

void eraseNode(int node);

void bypassNode(int node);

void runTarjan(int node);

bool checkNodeCanBeReduced(int node);

bool checkTarjan(int node);

bool reduceCORE();

bool reduceDOME();

bool reduceSCC();

int countSCC(int node);

long long getFitness(int node);

double getElapsed();

bool reduceDICLIQUE3();

void mergeNode(int node);

bool reduceDICLIQUE2();

bool reduceDICLIQUE1();

signed main(int argc, char **argv) {

    ofstream out("graph.out");
    if (argc != 4) {
        cout << "Incorrect number of arguments!\n";
        exit(0);
    }
    string input(argv[1]), output(argv[2]);
    inputFileName = input;
    outputFileName = output;
    SECONDS = atoi(argv[3]);
    solveTestcase();
    return 0;
}

bool checkNodeCanBeReduced(int node) {
    checkTime();
    if (!availableNode[node]) {
        return false;
    }
    if ((inDegreeSimple[node].empty() && degreeDouble[node].empty()) ||
        (outDegreeSimple[node].empty() && degreeDouble[node].empty())) {
        zeroDegreeNodes.emplace_back(node);
        return true;
    }
    if (edges.count(make_pair(node, node))) {
        selfLoopNodes.emplace_back(node);
        return true;
    }
    if (inDegreeSimple[node].size() + degreeDouble[node].size() == 1 ||
        outDegreeSimple[node].size() + degreeDouble[node].size() == 1) {
        oneDegreeNodes.emplace_back(node);
        return true;
    }
    return false;
}

void eraseEdge(int x, int y, int z) {
    checkTime();
    edges.erase(make_pair(x, y));
    outDegreeSimple[x].erase(y);
    degreeDouble[x].erase(y);
    inDegreeSimple[y].erase(x);
    degreeDouble[y].erase(x);
    if (edges.count(make_pair(y, x))) {
        edges.erase(make_pair(y, x));
        degreeDouble[x].erase(y);
        inDegreeSimple[x].erase(y);
        degreeDouble[y].erase(x);
        outDegreeSimple[y].erase(x);
    }
    if ((z == 1 || z == 3) && !checkNodeCanBeReduced(x)) {
        if (lastFitness[x] != -1) {
            availableNodes.erase(make_pair(lastFitness[x], x));
        }
        availableNodes.insert(make_pair((lastFitness[x] = getFitness(x)), x));
    }
    if ((z == 2 || z == 3) && !checkNodeCanBeReduced(y)) {
        if (lastFitness[y] != -1) {
            availableNodes.erase(make_pair(lastFitness[y], y));
        }
        availableNodes.insert(make_pair((lastFitness[y] = getFitness(y)), y));
    }
}

void addEdge(int x, int y) {
    checkTime();
    if (!edges.count(make_pair(y, x)) || x == y) {
        edges.insert(make_pair(x, y));
        inDegreeSimple[y].insert(x);
        outDegreeSimple[x].insert(y);
    } else {
        edges.insert(make_pair(x, y));
        inDegreeSimple[x].erase(y);
        outDegreeSimple[y].erase(x);
        degreeDouble[x].insert(y);
        degreeDouble[y].insert(x);
    }
}

void initializeSets() {
    checkTime();
    lastFitness.resize(n + 1, -1);
    visitedCORE.resize(n + 1, false);
    lowLevel.resize(n + 1, 0);
    currLevel.resize(n + 1, 0);
    inStack.resize(n + 1, false);
    whichSCC.resize(n + 1, 0);
    availableNode.resize(n + 1, true);
    inDegreeSimple.resize(n + 1, unordered_set<int>());
    degreeDouble.resize(n + 1, unordered_set<int>());
    outDegreeSimple.resize(n + 1, unordered_set<int>());
}

void clearSets() {
    checkTime();
    lastFitness.clear();
    visitedCORE.clear();
    whichSCC.clear();
    feedbackVertexSet.clear();
    availableNode.clear();
    selfLoopNodes.clear();
    zeroDegreeNodes.clear();
    oneDegreeNodes.clear();
    availableNodes.clear();
    candidatesNodes.clear();
    edges.clear();
    inDegreeSimple.clear();
    degreeDouble.clear();
    outDegreeSimple.clear();
}

void eraseNode(int node) {
    checkTime();
    if (!availableNode[node]) {
        return;
    }
    availableNode[node] = false;
    candidatesNodes.erase(node);
    availableNodes.erase(make_pair(lastFitness[node], node));
    while (!inDegreeSimple[node].empty()) {
        checkTime();
        int x = *inDegreeSimple[node].begin();
        inDegreeSimple[node].erase(inDegreeSimple[node].begin());
        outDegreeSimple[x].erase(node);
        edges.erase(make_pair(x, node));
        if (node != x && !checkNodeCanBeReduced(x)) {
            if (lastFitness[x] != -1) {
                availableNodes.erase(make_pair(lastFitness[x], x));
            }
            availableNodes.insert(make_pair((lastFitness[x] = getFitness(x)), x));
        }
    }
    while (!degreeDouble[node].empty()) {
        checkTime();
        int x = *degreeDouble[node].begin();
        degreeDouble[node].erase(degreeDouble[node].begin());
        degreeDouble[x].erase(node);
        edges.erase(make_pair(x, node));
        edges.erase(make_pair(node, x));
        if (node != x && !checkNodeCanBeReduced(x)) {
            if (lastFitness[x] != -1) {
                availableNodes.erase(make_pair(lastFitness[x], x));
            }
            availableNodes.insert(make_pair((lastFitness[x] = getFitness(x)), x));
        }
    }
    while (!outDegreeSimple[node].empty()) {
        checkTime();
        int x = *outDegreeSimple[node].begin();
        outDegreeSimple[node].erase(outDegreeSimple[node].begin());
        inDegreeSimple[x].erase(node);
        edges.erase(make_pair(node, x));
        if (node != x && !checkNodeCanBeReduced(x)) {
            if (lastFitness[x] != -1) {
                availableNodes.erase(make_pair(lastFitness[x], x));
            }
            availableNodes.insert(make_pair((lastFitness[x] = getFitness(x)), x));
        }
    }
}

void bypassNode(int node) {
    checkTime();
    if (!availableNode[node]) {
        return;
    }
    if (edges.count(make_pair(node, node))) {
        selfLoopNodes.emplace_back(node);
        return;
    }
    if ((inDegreeSimple[node].empty() && degreeDouble[node].empty()) ||
        (outDegreeSimple[node].empty() && degreeDouble[node].empty())) {
        zeroDegreeNodes.emplace_back(node);
        return;
    }
    if (inDegreeSimple[node].size() + degreeDouble[node].size() != 1 &&
        outDegreeSimple[node].size() + degreeDouble[node].size() != 1) {
        return;
    }
    availableNode[node] = false;
    candidatesNodes.erase(node);
    for (auto it :inDegreeSimple[node]) {
        checkTime();
        toBeErasedBypass.emplace_back(make_pair(it, node), 0);
        inNodes.emplace_back(it);
    }
    for (auto it :degreeDouble[node]) {
        checkTime();
        toBeErasedBypass.emplace_back(make_pair(it, node), 0);
        inNodes.emplace_back(it);
    }
    for (auto it :outDegreeSimple[node]) {
        checkTime();
        toBeErasedBypass.emplace_back(make_pair(node, it), 0);
        outNodes.emplace_back(it);
    }
    for (auto it :degreeDouble[node]) {
        checkTime();
        toBeErasedBypass.emplace_back(make_pair(node, it), 0);
        outNodes.emplace_back(it);
    }
    for (auto it : toBeErasedBypass) {
        checkTime();
        eraseEdge(it.first.first, it.first.second, it.second);
    }
    toBeErasedBypass.clear();
    for (auto it1 : inNodes) {
        checkTime();
        for (auto it2 : outNodes) {
            checkTime();
            addEdge(it1, it2);
            edges.insert(make_pair(it1, it2));
            if (it1 == it2) {
                selfLoopNodes.emplace_back(it1);
            }
            checkNodeCanBeReduced(it2);
            if (lastFitness[it2] != -1) {
                availableNodes.erase(make_pair(lastFitness[it2], it2));
            }
            availableNodes.insert(make_pair((lastFitness[it2] = getFitness(it2)), it2));
        }
        checkNodeCanBeReduced(it1);
        if (lastFitness[it1] != -1) {
            availableNodes.erase(make_pair(lastFitness[it1], it1));
        }
        availableNodes.insert(make_pair((lastFitness[it1] = getFitness(it1)), it1));
    }
    inNodes.clear();
    outNodes.clear();
}

void runTarjan(int node) {
    checkTime();
    stackTarjan.emplace_back(make_pair(node, outDegreeSimple[node].begin()), 0);
    for (; !stackTarjan.empty();) {
        checkTime();
        if (stackTarjan.back().first.second == outDegreeSimple[stackTarjan.back().first.first].begin() &&
            !stackTarjan.back().second) {
            lowLevel[stackTarjan.back().first.first] = ++sccIndex;
            currLevel[stackTarjan.back().first.first] = sccIndex;
            inStack[stackTarjan.back().first.first] = true;
            sccStack.emplace_back(stackTarjan.back().first.first);
        }

        if (stackTarjan.back().first.second != outDegreeSimple[stackTarjan.back().first.first].end() &&
            edges.count(make_pair(*stackTarjan.back().first.second, stackTarjan.back().first.first))) {
            stackTarjan.back().first.second++;
            continue;
        }

        if (stackTarjan.back().second &&
            stackTarjan.back().first.second != outDegreeSimple[stackTarjan.back().first.first].end()) {
            lowLevel[stackTarjan.back().first.first] = min(
                    lowLevel[stackTarjan.back().first.first],
                    lowLevel[*stackTarjan.back().first.second]);
            stackTarjan.back().first.second++;
            stackTarjan.back().second = 0;
            continue;
        }

        if (stackTarjan.back().first.second != outDegreeSimple[stackTarjan.back().first.first].end()) {
            if (!currLevel[*stackTarjan.back().first.second]) {
                stackTarjan.back().second = 1;
                stackTarjan.emplace_back(make_pair(*stackTarjan.back().first.second,
                                                   outDegreeSimple[*stackTarjan.back().first.second].begin()), 0);
                continue;
            } else {
                if (inStack[*stackTarjan.back().first.second]) {
                    lowLevel[stackTarjan.back().first.first] = min(
                            lowLevel[stackTarjan.back().first.first],
                            lowLevel[*stackTarjan.back().first.second]);
                }
                stackTarjan.back().first.second++;
                stackTarjan.back().second = 0;
                continue;
            }
        } else {
            if (lowLevel[stackTarjan.back().first.first] ==
                currLevel[stackTarjan.back().first.first]) {
                ++sccCounter;
                int currNode = -1;
                while (currNode != stackTarjan.back().first.first) {
                    checkTime();
                    currNode = sccStack.back();
                    sccStack.pop_back();
                    inStack[currNode] = false;
                    whichSCC[currNode] = sccCounter;
                }
            }
            stackTarjan.pop_back();
        }
    }
}

bool checkTarjan(int node) {
    checkTime();
    stackTarjan.emplace_back(make_pair(node, outDegreeSimple[node].begin()), 0);
    for (; !stackTarjan.empty();) {
        checkTime();
        if (stackTarjan.back().first.second == outDegreeSimple[stackTarjan.back().first.first].begin() &&
            !stackTarjan.back().second) {
            lowLevel[stackTarjan.back().first.first] = ++sccIndex;
            currLevel[stackTarjan.back().first.first] = sccIndex;
            inStack[stackTarjan.back().first.first] = true;
            sccStack.emplace_back(stackTarjan.back().first.first);
        }
        if (stackTarjan.back().first.second != outDegreeSimple[stackTarjan.back().first.first].end() &&
            edges.count(make_pair(*stackTarjan.back().first.second, stackTarjan.back().first.first))) {
            stackTarjan.back().first.second++;
            continue;
        }

        if (stackTarjan.back().second &&
            stackTarjan.back().first.second != outDegreeSimple[stackTarjan.back().first.first].end()) {
            lowLevel[stackTarjan.back().first.first] = min(
                    lowLevel[stackTarjan.back().first.first],
                    lowLevel[*stackTarjan.back().first.second]);
            if (lowLevel[stackTarjan.back().first.first] != currLevel[stackTarjan.back().first.first]) {
                sccStack.clear();
                stackTarjan.clear();
                return false;
            }
            stackTarjan.back().first.second++;
            stackTarjan.back().second = 0;
            continue;
        }

        if (stackTarjan.back().first.second != outDegreeSimple[stackTarjan.back().first.first].end()) {
            if (!currLevel[*stackTarjan.back().first.second]) {
                stackTarjan.back().second = 1;
                stackTarjan.emplace_back(make_pair(*stackTarjan.back().first.second,
                                                   outDegreeSimple[*stackTarjan.back().first.second].begin()), 0);
                continue;
            } else {
                if (inStack[*stackTarjan.back().first.second]) {
                    lowLevel[stackTarjan.back().first.first] = min(
                            lowLevel[stackTarjan.back().first.first],
                            lowLevel[*stackTarjan.back().first.second]);
                }
                if (lowLevel[stackTarjan.back().first.first] != currLevel[stackTarjan.back().first.first]) {
                    sccStack.clear();
                    stackTarjan.clear();
                    return false;
                }
                stackTarjan.back().first.second++;
                stackTarjan.back().second = 0;
                continue;
            }
        } else {
            if (lowLevel[stackTarjan.back().first.first] ==
                currLevel[stackTarjan.back().first.first]) {
                ++sccCounter;
                int currNode = -1;
                while (currNode != stackTarjan.back().first.first) {
                    checkTime();
                    currNode = sccStack.back();
                    sccStack.pop_back();
                    inStack[currNode] = false;
                    whichSCC[currNode] = sccCounter;
                }
            }
            stackTarjan.pop_back();
        }
    }
    return true;
}

bool reduceCORE() {
    checkTime();
    for (auto it : candidatesNodes) {
        checkTime();
        visitedCORE[it] = false;
    }
    checkTime();
    candidatesSorted.reserve(candidatesNodes.size());
    for (auto node : candidatesNodes) {
        checkTime();
        candidatesSorted.emplace_back(node);
    }
    checkTime();
    sort(candidatesSorted.begin(), candidatesSorted.end(), [](const int i, const int j) {
        return degreeDouble[i].size() < degreeDouble[j].size() ||
               (degreeDouble[i].size() == degreeDouble[j].size() &&
                min(inDegreeSimple[i].size(), outDegreeSimple[i].size()) <
                min(inDegreeSimple[j].size(), outDegreeSimple[j].size()));
    });
    checkTime();
    bool ret = false;
    for (auto node : candidatesSorted) {
        checkTime();
        if (visitedCORE[node]) continue;

        if (!outDegreeSimple[node].empty() && !inDegreeSimple[node].empty()) {
            visitedCORE[node] = true;
            continue;
        }
        for (auto it : degreeDouble[node]) {
            checkTime();
            cliqueCORE.insert(it);
        }
        bool isCore = true;
        if (cliqueCORE.empty()) {
            isCore = false;
        }
        cliqueCORE.insert(node);
        for (auto it : cliqueCORE) {
            checkTime();
            int sz = 1;
            if (isCore) {
                for (auto it3 : degreeDouble[it]) {
                    checkTime();
                    if (cliqueCORE.count(it3)) {
                        ++sz;
                    }
                }
                if (sz != cliqueCORE.size()) {
                    isCore = false;
                }
            }
            visitedCORE[it] = true;
        }
        visitedCORE[node] = true;
        if (isCore) {
            for (auto it : cliqueCORE) {
                checkTime();
                eraseNode(it);
                if (it != node) {
                    feedbackVertexSet.insert(it);
                }
            }
            ret = true;
        }
        cliqueCORE.clear();
    }
    candidatesSorted.clear();
    return ret;
}

bool reduceDOME() {
    checkTime();
    for (auto node : candidatesNodes) {
        checkTime();
        for (auto it : outDegreeSimple[node]) {
            checkTime();
            if (inDegreeSimple[it].size() >= inDegreeSimple[node].size() && inDegreeSimple[node].size() <= 50) {
                bool status = true;
                for (auto it2 : inDegreeSimple[node]) {
                    checkTime();
                    if (!inDegreeSimple[it].count(it2)) {
                        status = false;
                        break;
                    }
                }
                if (status) {
                    toBeErasedDOME.emplace_back(node, it);
                    continue;
                }
            }
            if (outDegreeSimple[node].size() >= outDegreeSimple[it].size() && outDegreeSimple[it].size() <= 50) {
                bool status = true;
                for (auto it2 : outDegreeSimple[it]) {
                    checkTime();
                    if (!outDegreeSimple[node].count(it2)) {
                        status = false;
                        break;
                    }
                }
                if (status) {
                    toBeErasedDOME.emplace_back(node, it);
                    continue;
                }
            }
        }
    }
    bool ret = !toBeErasedDOME.empty();
    for (auto it : toBeErasedDOME) {
        checkTime();
        eraseEdge(it.first, it.second, 3);
    }
    toBeErasedDOME.clear();
    checkTime();
    return ret;
}

int countSCC(int node) {
    checkTime();
    sccIndex = 0;
    sccCounter = 0;
    for (auto it : candidatesNodes) {
        checkTime();
        lowLevel[it] = 0;
        currLevel[it] = 0;
        inStack[it] = false;
    }
    bool ret = checkTarjan(node);
    sccIndex = 0;
    sccCounter = 0;
    sccStack.clear();
    return ret;
}

bool reduceSCC() {
    checkTime();
    sccIndex = 0;
    sccCounter = 0;
    for (auto it : candidatesNodes) {
        checkTime();
        lowLevel[it] = 0;
        currLevel[it] = 0;
        inStack[it] = false;
    }
    for (auto it : candidatesNodes) {
        checkTime();
        if (!currLevel[it]) {
            checkTime();
            runTarjan(it);
        }
    }
    for (auto it : edges) {
        checkTime();
        if (edges.count(make_pair(it.second, it.first))) continue;
        if (whichSCC[it.first] != whichSCC[it.second]) {
            toBeErasedSCC.emplace_back(it);
        }
    }
    for (auto it : toBeErasedSCC) {
        checkTime();
        eraseEdge(it.first, it.second, 3);
    }
    bool ret = !toBeErasedSCC.empty();
    toBeErasedSCC.clear();
    sccIndex = 0;
    sccCounter = 0;
    sccStack.clear();
    return ret;
}

void doBasicReductions() {
    checkTime();
    bool change = true;
    while (change) {
        checkTime();
        change = false;
        change |= !selfLoopNodes.empty();
        while (!selfLoopNodes.empty()) {
            checkTime();
            int node = selfLoopNodes.back();
            selfLoopNodes.pop_back();
            if (!edges.count(make_pair(node, node))) {
                continue;
            }
            eraseNode(node);
            feedbackVertexSet.insert(node);
        }
        change |= !zeroDegreeNodes.empty();
        while (!zeroDegreeNodes.empty()) {
            checkTime();
            int node = zeroDegreeNodes.back();
            zeroDegreeNodes.pop_back();
            if ((!degreeDouble[node].empty() || !inDegreeSimple[node].empty()) &&
                (!outDegreeSimple[node].empty() || !degreeDouble[node].empty())) {
                continue;
            }
            eraseNode(node);
        }
        change |= !oneDegreeNodes.empty();
        while (!oneDegreeNodes.empty()) {
            checkTime();
            int node = oneDegreeNodes.back();
            oneDegreeNodes.pop_back();
            bypassNode(node);
        }
    }
}

void loop() {
    bool change = true;
    int count = 0;
    while (change) {
        checkTime();
        change = false;
        change |= reduceSCC();
        doBasicReductions();
        change |= reduceCORE();
        doBasicReductions();
        change |= reduceDOME();
        doBasicReductions();
        change |= reduceDICLIQUE1();
        doBasicReductions();
        change |= reduceDICLIQUE2();
        doBasicReductions();
        change |= reduceDICLIQUE3();
        doBasicReductions();
    }
}

void findDFVS() {
    checkTime();
    doBasicReductions();
    int edgesCount = (int) edges.size();
    currentErased = 0;
    loop();
    while (!availableNodes.empty()) {
        checkTime();
        pair<int, long long> topNode = make_pair((*availableNodes.begin()).second, (*availableNodes.begin()).first);
        availableNodes.erase(availableNodes.begin());
        if (!availableNode[topNode.first]) {
            continue;
        }
        ++currentErased;
        eraseNode(topNode.first);
        doBasicReductions();
        if ((edges.size() * 10 < edgesCount * 9 && firstTime) ||
            (edges.size() * 4 < edgesCount * 3 && !firstTime)) {
            loop();
            edgesCount = edges.size();
        }
        feedbackVertexSet.insert(topNode.first);
    }
    lastFeedbackVertexSet = feedbackVertexSet;
    if (bestFeedbackVertexSet.size() > feedbackVertexSet.size()) {
        changed = (int) bestFeedbackVertexSet.size() - (int) feedbackVertexSet.size();
        bestFeedbackVertexSet = feedbackVertexSet;
    } else {
        changed = 0;
    }

}

void readData() {
    ifstream in(inputFileName);
    int t;
    while (getline(in, s)) {
        deque<char> input;
        for (auto it : s) {
            input.push_back(it);
        }
        while (!input.empty() && input.front() == ' ') {
            input.pop_front();
        }
        s.clear();
        for (char i : input) {
            s.push_back(i);
        }
        if (s.empty() || s[0] == '%') continue;
        istringstream is(s);
        is >> n >> m >> t;
        break;
    }
    initializeSets();
    for (int j = 1; j <= n; ++j) {
        getline(in, s);
        deque<char> input;
        for (auto it : s) {
            input.push_back(it);
        }
        while (!input.empty() && input.front() == ' ') {
            input.pop_front();
        }
        s.clear();
        for (char i : input) {
            s.push_back(i);
        }
        if (!s.empty() && s[0] == '%') {
            j--;
            continue;
        }
        istringstream is(s);
        while (is >> t) {
            addEdge(j, t);
        }
    }
    for (int i = 1; i < n; ++i) {
        bestFeedbackVertexSet.insert(i);
    }
    in.close();
    if (n == 0) {
        exit(0);
    }
}

void createInitialDFVS() {
    checkTime();
    candidatesNodes = candidatesNodesReduced;
    inDegreeSimple = inDegreeReducedSimple;
    degreeDouble = degreeReducedDouble;
    outDegreeSimple = outDegreeReducedSimple;
    for (auto it : edgesReduced) {
        checkTime();
        edges.insert(it);
    }
    availableNode = availableNodeReduced;
    for (auto x : candidatesNodes) {
        checkTime();
        if (!checkNodeCanBeReduced(x)) {
            if (lastFitness[x] != -1) {
                availableNodes.erase(make_pair(lastFitness[x], x));
            }
            availableNodes.insert(make_pair(getFitness(x), x));
            lastFitness[x] = getFitness(x);
        }
    }
    findDFVS();
    clearSets();
    initializeSets();
}

void improveFeedbackVertexSet() {
    auto currentTime = getElapsed();
    checkTime();
    availableNode = availableNodeReduced;
    for (auto it : candidatesNodesReduced) {
        checkTime();
        if (!lastFeedbackVertexSet.count(it)) {
            candidatesNodes.insert(it);
        } else {
            availableNode[it] = false;
        }
    }
    for (auto it : edgesReduced) {
        checkTime();
        bool node1 = false, node2 = false;
        if (candidatesNodes.count(it.first)) {
            node1 = true;
        }
        if (candidatesNodes.count(it.second)) {
            node2 = true;
        }
        if (!node1 || !node2) {
            continue;
        }
        edges.insert(it);
    }
    for (auto it : edges) {
        checkTime();
        if (edges.count(make_pair(it.second, it.first))) {
            degreeDouble[it.first].insert(it.second);
            degreeDouble[it.second].insert(it.first);
        } else {
            outDegreeSimple[it.first].insert(it.second);
            inDegreeSimple[it.second].insert(it.first);
        }
    }

    localDFVS.reserve(lastFeedbackVertexSet.size());
    for (auto it : lastFeedbackVertexSet) {
        checkTime();
        localDFVS.emplace_back(it);
    }
    sort(localDFVS.begin(), localDFVS.end(), [](const int i, const int j) {
        return 1LL * inDegreeReducedSimple[i].size() * outDegreeReducedSimple[i].size() >
               1LL * inDegreeReducedSimple[j].size() * outDegreeReducedSimple[j].size();
    });
    while (!localDFVS.empty()) {
        auto currTime = getElapsed();
        /*
         if (currTime - currentTime > 5. && firstTime) {
             break;
         }
        */

        if (currentTime > SECONDS - 20) {
            if (lastFeedbackVertexSet.size() < bestFeedbackVertexSet.size()) {
                bestFeedbackVertexSet = lastFeedbackVertexSet;
            }
        }

        checkTime();
        int node = localDFVS.back();
        localDFVS.pop_back();
        bool dag = true;
        for (auto it : degreeReducedDouble[node]) {
            checkTime();
            if (candidatesNodes.count(it)) {
                dag = false;
                break;
            }
        }
        if (!dag) {
            continue;
        }
        for (auto it : inDegreeReducedSimple[node]) {
            checkTime();
            if (candidatesNodes.count(it)) {
                inDegreeSimple[node].insert(it);
                outDegreeSimple[it].insert(node);
                edges.insert(make_pair(it, node));
            }
        }
        for (auto it : outDegreeReducedSimple[node]) {
            checkTime();
            if (candidatesNodes.count(it)) {
                outDegreeSimple[node].insert(it);
                inDegreeSimple[it].insert(node);
                edges.insert(make_pair(node, it));
            }
        }
        candidatesNodes.insert(node);
        availableNode[node] = true;
        if (countSCC(node)) {
            lastFeedbackVertexSet.erase(node);
        } else {
            for (auto it : inDegreeSimple[node]) {
                checkTime();
                if (it != node) {
                    outDegreeSimple[it].erase(node);
                    edges.erase(make_pair(it, node));
                }
            }
            inDegreeSimple[node].clear();
            for (auto it : outDegreeSimple[node]) {
                checkTime();
                if (it != node) {
                    inDegreeSimple[it].erase(node);
                    edges.erase(make_pair(node, it));
                }
            }
            outDegreeSimple[node].clear();
            edges.erase(make_pair(node, node));
            candidatesNodes.erase(node);
            availableNode[node] = false;
        }
    }
    localDFVS.clear();
    clearSets();
    initializeSets();
    if (lastFeedbackVertexSet.size() < bestFeedbackVertexSet.size()) {
        bestFeedbackVertexSet = lastFeedbackVertexSet;
    }
    clearSets();
    initializeSets();
}

void doLocalSearch() {
    checkTime();
    checkTime();
    for (auto node : bestFeedbackVertexSet) {
        checkTime();
        local.emplace_back(node);
    }
    checkTime();
    unsigned seed = customRand();
    fitnessType = (int) seed % 2 + 1;

    if (!local.empty()) {
        for (int i = 0; i < local.size(); i++) {
            int j = customRand() % ((int) local.size());
            swap(local[i], local[j]);
        }
    }
    int toBeErasedCounter = (int) local.size() * chunk[ratioIndex] / (chunk[ratioIndex] + 1);
    if (bestFeedbackVertexSet.size() < 250 && seed % 2 == 1) {
        toBeErasedCounter = (int) local.size() * 2 / 3;
    }
    while (toBeErasedCounter--) {
        checkTime();
        int node = local.back();
        local.pop_back();
        localSet.insert(node);
        feedbackVertexSet.insert(node);
    }
    local.clear();
    availableNode = availableNodeReduced;
    for (auto it : candidatesNodesReduced) {
        checkTime();
        if (!localSet.count(it)) {
            candidatesNodes.insert(it);
        } else {
            availableNode[it] = false;
        }
    }
    for (auto it : edgesReduced) {
        checkTime();
        bool node1 = false, node2 = false;
        if (candidatesNodes.count(it.first)) {
            node1 = true;
        }
        if (candidatesNodes.count(it.second)) {
            node2 = true;
        }
        if (!node1 || !node2) {
            continue;
        }
        edges.insert(it);
    }
    for (auto it : edges) {
        checkTime();
        if (edges.count(make_pair(it.second, it.first))) {
            degreeDouble[it.first].insert(it.second);
            degreeDouble[it.second].insert(it.first);
        } else {
            outDegreeSimple[it.first].insert(it.second);
            inDegreeSimple[it.second].insert(it.first);
        }
    }
    loop();

    for (auto x : candidatesNodes) {
        checkTime();
        if (!checkNodeCanBeReduced(x)) {
            if (lastFitness[x] != -1) {
                availableNodes.erase(make_pair(lastFitness[x], x));
            }
            availableNodes.insert(make_pair(getFitness(x), x));
            lastFitness[x] = getFitness(x);
        }
    }
    local.clear();
    localSet.clear();
    findDFVS();
    clearSets();
    initializeSets();
}

double getElapsed() {
    auto end = std::chrono::high_resolution_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin_);
    double sec = elapsed.count() * 1e-9;
    return sec;
}

void checkTime() {
    auto end = std::chrono::high_resolution_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin_);
    double sec = elapsed.count() * 1e-9;
    if (sec >= SECONDS - 15) {
        string path_output =
                R"(C:\Users\andre\OneDrive\Desktop\PACE2022\adhoc-results\grader_test)" + to_string(testNo) +
                ".out";
        ofstream out(outputFileName);
        ios_base::sync_with_stdio(false);
        out.tie();
        for (auto it: feedbackVertexSetReduced) {
            output += to_string(it) + '\n';
        }
        for (auto node : bestFeedbackVertexSet) {
            output += to_string(node) + '\n';
        }
        out << output;
        out.close();
        output.clear();
        exit(0);
    }
}

long long getFitness(int node) {
    if (fitnessType == 1) {
        return 1LL * degreeDouble[node].size() * (long long) 1e11 +
               1LL * (inDegreeSimple[node].size()) * (outDegreeSimple[node].size());
    }
    if (fitnessType == 2) {
        return 1LL * (inDegreeSimple[node].size() + degreeDouble[node].size()) *
               (outDegreeSimple[node].size() + degreeDouble[node].size());
    }
    if (fitnessType == 3) {
        return 1LL * (inDegreeSimple[node].size() + 2 * degreeDouble[node].size()) *
               (outDegreeSimple[node].size() + 2 * degreeDouble[node].size());
    }
    return 0;
}

void solveTestcase() {
    begin_ = std::chrono::high_resolution_clock::now();
    readData();
    for (int i = 1; i <= n; ++i) {
        checkNodeCanBeReduced(i);
    }
    for (int i = 1; i <= n; ++i) {
        candidatesNodes.insert(i);
    }
    loop();
    candidatesNodesReduced = candidatesNodes;
    inDegreeReducedSimple = inDegreeSimple;
    degreeReducedDouble = degreeDouble;
    outDegreeReducedSimple = outDegreeSimple;
    feedbackVertexSetReduced = feedbackVertexSet;
    for (auto it : edges) {
        edgesReduced.emplace_back(it);
    }
    availableNodeReduced = availableNode;
    feedbackVertexSet.clear();
    for (fitnessType = 1; fitnessType <= 1; ++fitnessType) {
        checkTime();
        createInitialDFVS();
        clearSets();
        initializeSets();
        improveFeedbackVertexSet();
    }
    if (bestFeedbackVertexSet.size() > 10000) {
        ratioIndex = 2;
    }
    if (bestFeedbackVertexSet.size() > 30000) {
        ratioIndex = 4;
    }

    firstTime = 1;
    clearSets();
    initializeSets();
    for (;;) {
        auto currentTime = getElapsed();
        checkTime();
        doLocalSearch();
        auto currTime = getElapsed();
        if (changed < 5) {
            improveFeedbackVertexSet();
        }
        if (currTime - currentTime > 8.) {
            ratioIndex = min(ratioIndex + 1, (int) chunk.size() - 1);
        }
    }
    ofstream out(outputFileName);
    for (auto it: feedbackVertexSetReduced) {
        output += to_string(it) + '\n';
    }
    for (auto node : bestFeedbackVertexSet) {
        output += to_string(node) + '\n';
    }
    out << output;
    out.close();
    output.clear();
}


bool reduceDICLIQUE3() {
    bool ret = false;
    ll = candidatesNodes;
    for (auto it : ll) {
        if (!availableNode[it]) {
            continue;
        }
        if (edges.count(make_pair(it, it))) {
            continue;
        }
        if (!degreeDouble[it].empty()) {
            continue;
        }
        for (auto it2 : inDegreeSimple[it]) {
            checkTime();
            candidatesSortedSet.insert(it2);
        }
        for (auto it2 : outDegreeSimple[it]) {
            checkTime();
            candidatesSortedSet.insert(it2);
        }
        bool ok = true;
        for (auto &i : cl3) {
            checkTime();
            if (candidatesSortedSet.empty()) {
                candidatesSortedSet.clear();
                for (auto &it2 : cl3) {
                    checkTime();
                    it2.clear();
                }
                ok = false;
                break;
            }
            int node = *candidatesSortedSet.begin();
            candidatesSortedSet.erase(node);
            i.insert(node);
            for (auto it2 : candidatesSortedSet) {
                checkTime();
                if (edges.count(make_pair(node, it2)) && edges.count(make_pair(it2, node))) {
                    i.insert(it2);
                    toBeErasedSet.emplace_back(it2);
                }
            }
            for (auto it2 : toBeErasedSet) {
                checkTime();
                candidatesSortedSet.erase(it2);
            }
            toBeErasedSet.clear();
        }
        if (!ok) {
            continue;
        }
        if (!candidatesSortedSet.empty()) {
            candidatesSortedSet.clear();
            for (auto &it2 : cl3) {
                checkTime();
                it2.clear();
            }
            continue;
        }
        bool clOK[3] = {true, true, true}, okIsh = true;
        for (int i = 0; i < 3 && okIsh; ++i) {
            checkTime();
            for (auto it3 : cl3[i]) {
                checkTime();
                for (auto it4 : cl3[i]) {
                    checkTime();
                    if (it3 == it4) {
                        continue;
                    }
                    if (!edges.count(make_pair(it3, it4)) || !edges.count(make_pair(it4, it3))) {
                        clOK[i] = false;
                        break;
                    }
                }
                if (!clOK[i]) {
                    break;
                }
            }
            if (!clOK[i]) {
                okIsh = false;
                for (auto &it2 : cl3) {
                    checkTime();
                    it2.clear();
                }
                candidatesSortedSet.clear();
                break;
            }
        }
        if (!okIsh) {
            continue;
        }
        mergeNode(it);
        ret = true;
        for (auto &it2 : cl3) {
            checkTime();
            it2.clear();
        }
        candidatesSortedSet.clear();
    }
    return ret;
}

void mergeNode(int node) {
    checkTime();

    availableNode[node] = false;
    candidatesNodes.erase(node);
    for (auto it :inDegreeSimple[node]) {
        checkTime();
        toBeErasedBypass.emplace_back(make_pair(it, node), 0);
        inNodes.emplace_back(it);
    }
    for (auto it :degreeDouble[node]) {
        checkTime();
        toBeErasedBypass.emplace_back(make_pair(it, node), 0);
        inNodes.emplace_back(it);
    }
    for (auto it :outDegreeSimple[node]) {
        checkTime();
        toBeErasedBypass.emplace_back(make_pair(node, it), 0);
        outNodes.emplace_back(it);
    }
    for (auto it :degreeDouble[node]) {
        checkTime();
        toBeErasedBypass.emplace_back(make_pair(node, it), 0);
        outNodes.emplace_back(it);
    }
    for (auto it : toBeErasedBypass) {
        checkTime();
        eraseEdge(it.first.first, it.first.second, it.second);
    }
    toBeErasedBypass.clear();
    for (auto it1 : inNodes) {
        checkTime();
        for (auto it2 : outNodes) {
            checkTime();
            addEdge(it1, it2);
            edges.insert(make_pair(it1, it2));
            if (it1 == it2) {
                selfLoopNodes.emplace_back(it1);
            }
            checkNodeCanBeReduced(it2);
            if (lastFitness[it2] != -1) {
                availableNodes.erase(make_pair(lastFitness[it2], it2));
            }
            availableNodes.insert(make_pair((lastFitness[it2] = getFitness(it2)), it2));
        }
        checkNodeCanBeReduced(it1);
        if (lastFitness[it1] != -1) {
            availableNodes.erase(make_pair(lastFitness[it1], it1));
        }
        availableNodes.insert(make_pair((lastFitness[it1] = getFitness(it1)), it1));
    }
    inNodes.clear();
    outNodes.clear();
}


bool reduceDICLIQUE2() {
    bool ret = false;
    ll = candidatesNodes;
    for (auto it : ll) {
        checkTime();
        if (!availableNode[it]) {
            continue;
        }
        if (edges.count(make_pair(it, it))) {
            doBasicReductions();
            continue;
        }
        if (degreeDouble[it].size() > 50 || inDegreeSimple[it].size() > 50 || outDegreeSimple[it].size() > 50) {
            continue;
        }
        bool doubleOK = true;
        for (auto it2 : degreeDouble[it]) {
            for (auto it3 : degreeDouble[it]) {
                if (it2 == it3) {
                    continue;
                }
                if (!edges.count(make_pair(it2, it3)) || !edges.count(make_pair(it3, it2))) {
                    doubleOK = false;
                    break;
                }
            }
            if (!doubleOK) {
                break;
            }
        }
        if (!doubleOK) {
            continue;
        }
        for (auto it2 : inDegreeSimple[it]) {
            bool isCliqueOne = true;
            for (auto it3 : degreeDouble[it]) {
                if (!edges.count(make_pair(it2, it3)) || !edges.count(make_pair(it3, it2))) {
                    isCliqueOne = false;
                    break;
                }
            }
            if (!isCliqueOne) {
                cl2[1].insert(it2);
            } else {
                set1.insert(it2);
            }
        }
        for (auto it2 : outDegreeSimple[it]) {
            bool isCliqueOne = true;
            for (auto it3 : degreeDouble[it]) {
                if (!edges.count(make_pair(it2, it3)) || !edges.count(make_pair(it3, it2))) {
                    isCliqueOne = false;
                    break;
                }
            }
            if (!isCliqueOne) {
                cl2[1].insert(it2);
            } else {
                set1.insert(it2);
            }
        }
        bool simpleOK = true;
        for (auto it2 : cl2[1]) {
            for (auto it3 : cl2[1]) {
                if (!edges.count(make_pair(it2, it3)) || !edges.count(make_pair(it3, it2))) {
                    simpleOK = false;
                    continue;
                }
            }
            if (!simpleOK) {
                break;
            }
        }
        if (!simpleOK) {
            set1.clear();
            cl2[1].clear();
            continue;
        }
        bool change = true, diClique = true;
        while (change) {
            change = false;
            vector<int> toBeErased;
            for (auto it2 : set1) {
                bool ok[2] = {true, true};
                for (int i = 0; i < 2; ++i) {
                    for (auto it3 : cl2[i]) {
                        if (!edges.count(make_pair(it2, it3)) || !edges.count(make_pair(it3, it2))) {
                            ok[i] = false;
                            break;
                        }
                    }
                    if (!ok[i]) {
                        break;
                    }
                }
                if (ok[0] && ok[1]) {
                    continue;
                }
                if (!ok[0] && !ok[1]) {
                    diClique = false;
                    break;
                }
                change = true;
                ok[0] ? cl2[0].insert(it2) : cl2[1].insert(it2);
                toBeErased.emplace_back(it2);
            }
            while (!toBeErased.empty()) {
                set1.erase(toBeErased.back());
                toBeErased.pop_back();
            }
        }
        cl2[0].clear();
        cl2[1].clear();
        if (!diClique) {
            set1.clear();
            continue;
        }
        if (set1.empty()) {
            mergeNode(it);
            ret = true;
            continue;
        } else {
            continue;
        }
        vector<pair<int, int>> nodes;
        for (auto it2 : set1) {
            int counter = 0;
            for (auto it3 : set1) {
                if (edges.count(make_pair(it2, it3)) && edges.count(make_pair(it3, it2))) {
                    ++counter;
                }
            }
            nodes.emplace_back(it2, counter);
        }
        sort(nodes.begin(), nodes.end(),
             [](const pair<int, int> &i, const pair<int, int> &j) { return i.second < j.second; });
        for (auto it2 : set1) {
            if (it2 == nodes[0].first ||
                (edges.count(make_pair(nodes[0].first, it2)) && edges.count(make_pair(it2, nodes[0].first)))) {
                cl2[0].insert(it2);
            } else {
                cl2[1].insert(it2);
            }
        }
        set1.clear();
        for (int i = 0; i < 2 && diClique; ++i) {
            for (auto it2 : cl2[i]) {
                for (auto it3 : cl2[i]) {
                    if (!edges.count(make_pair(it2, it3)) || !edges.count(make_pair(it3, it2))) {
                        diClique = false;
                    }
                }
                if (!diClique) {
                    break;
                }
            }
        }
        cl2[0].clear();
        cl2[1].clear();
        nodes.clear();
        if (diClique) {
            mergeNode(it);
        }
    }
    return ret;
}

bool reduceDICLIQUE1() {
    bool ret = false;
    for (auto it : candidatesNodes) {
        checkTime();
        candidatesSorted.emplace_back(it);
    }
    sort(candidatesSorted.begin(), candidatesSorted.end(), [](const int i, const int j) {
        return degreeDouble[i].size() + min(inDegreeSimple[i].size(), outDegreeSimple[i].size()) <
               degreeDouble[j].size() + min(inDegreeSimple[j].size(), outDegreeSimple[j].size());
    });
    for (auto it : candidatesSorted) {
        checkTime();
        if (!availableNode[it]) {
            continue;
        }
        if (edges.count(make_pair(it, it))) {
            doBasicReductions();
            continue;
        }
        if (degreeDouble.size() > 50) {
            continue;
        }
        bool doubleOK = true;
        for (auto it1 : degreeDouble[it]) {
            checkTime();
            for (auto it2 : degreeDouble[it]) {
                checkTime();
                if (it1 == it2) {
                    continue;
                }
                if (!edges.count(make_pair(it1, it2)) || !edges.count(make_pair(it2, it1))) {
                    doubleOK = false;
                    break;
                }
            }
            if (!doubleOK) {
                break;
            }
        }
        if (!doubleOK) {
            continue;
        }
        if (inDegreeSimple[it].empty() || outDegreeSimple[it].empty()) {
            mergeNode(it);
            ret = true;
            continue;
        }
        continue;
        bool inOK = true;
        for (auto it1 : inDegreeSimple[it]) {
            checkTime();
            for (auto it2 : inDegreeSimple[it]) {
                checkTime();
                if (!edges.count(make_pair(it1, it2)) || !edges.count(make_pair(it2, it1))) {
                    inOK = false;
                    break;
                }
            }
            if (!inOK) {
                break;
            }
        }
        if (inOK) {
            for (auto it1 : inDegreeSimple[it]) {
                checkTime();
                for (auto it2 : degreeDouble[it]) {
                    checkTime();
                    if (!edges.count(make_pair(it1, it2)) || !edges.count(make_pair(it2, it1))) {
                        inOK = false;
                        break;
                    }
                }
                if (!inOK) {
                    break;
                }
            }
        }
        if (inOK) {
            mergeNode(it);
            ret = true;
            continue;
        }
        bool outOK = true;
        for (auto it1 : outDegreeSimple[it]) {
            checkTime();
            for (auto it2 : outDegreeSimple[it]) {
                checkTime();
                if (!edges.count(make_pair(it1, it2)) || !edges.count(make_pair(it2, it1))) {
                    outOK = false;
                    break;
                }
            }
            if (!outOK) {
                break;
            }
        }
        if (outOK) {
            for (auto it1 : outDegreeSimple[it]) {
                checkTime();
                for (auto it2 : degreeDouble[it]) {
                    checkTime();
                    if (!edges.count(make_pair(it1, it2)) || !edges.count(make_pair(it2, it1))) {
                        outOK = false;
                        break;
                    }
                }
                if (!outOK) {
                    break;
                }
            }
        }
        if (outOK) {
            mergeNode(it);
            ret = true;
            continue;
        }
    }
    candidatesSorted.clear();
    return ret;
}
