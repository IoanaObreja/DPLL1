#include <fstream>
#include <cstdlib>
#include <list>
#include <map>
#include <chrono>
using namespace std::chrono;
using namespace std;
ifstream f ("input.in");
ofstream g ("output.out");

int clauses, variables;
// keep track of number of apparitions for each literal in a map
map<int, int> var_app;

void read(int &variables, int &clauses, list< list<int> > &formula) {

    // store the formula in a list of lists
    // read e
    int x;
    f>>variables>>clauses;
    for(int i=0;i<clauses;i++) {
        list<int> clause;
        do {
            f>>x;
            clause.push_back(x);
            var_app[x]++;
        }while(x!=0);
        formula.push_back(clause);
    }
}

int find_unit_clause(list< list<int> > formula) {

    for(auto& clause: formula)
        if(clause.size() == 2)
            return clause.front();
    return 0;
}

int find_pure_literal(list<list<int>> formula) {

    for(int i=1;i<=variables;i++) {
        if(var_app[i] > 0 && var_app[(-1)*i] == 0)
            return i;
        else
            if(var_app[(-1)*i] > 0 && var_app[i] == 0)
                return (-1)*i;
    }
    return 0;
}


list<list<int>> unit_propagate(list<list<int>> formula, int literal) {

    /// search for the literal in each clause
    /// delete clauses that contain the literal
    /// delete the negated literal

    for(auto& clause: formula) {
        for(auto& lit: clause) {
            if(lit == (-1)*literal) {
                var_app[lit]--;
                clause.remove(lit);
            }
            else if(lit == literal){
                // clause.erase(clause.begin(), clause.end());
                for(auto& lit2: clause) {
                    var_app[lit2]--;
                    clause.remove(lit2);
                }
                formula.remove(clause);
            }
        }
    }
    return formula;
}

list<list<int>> pure_literal(list<list<int>> formula, int literal) {

    /// delete the clauses that contain a pure literal
    for(auto& clause: formula) {
        for(auto& lit: clause) {
            if(lit == literal) {
                // clause.erase(clause.begin(), clause.end());
                for(auto& lit2: clause) {
                    var_app[lit2]--;
                    clause.remove(lit2);
                }
                formula.remove(clause);
            }
        }
    }
    return formula;
}

void print(list<list<int>> formula) {

    //int i=1;
    for(auto& clause: formula) {
        //g<<i++<<". ";
        for(auto& lit: clause)
            g<<lit<<' ';
        g<<'\n';
    }
    g<<'\n';
}

bool empty_clause(list<list <int>> formula) {

    for(auto& clause: formula)
        if(clause.size() == 1)
            return true;
    return false;
}


void print_assignment(list<int> assignment) {

    int v[variables+1];
    for(int i=1;i<=variables;i++)
        v[i] = 0;
    int nr=1;
    for(auto& lit: assignment) {
        g<<lit<<' ';
        if(nr++ % 10 == 0) g<<'\n';
        v[abs(lit)] = 1;
    }
    for(int i=1;i<=variables;i++)
        if(v[i] == 0) {
            g<<i<<' ';
            if(nr++ % 10 == 0) g<<'\n';
        }
    g<<'\n';
}

bool empty_formula(list<list<int>> formula) {

    for(auto& clause: formula)
        if(clause.size() > 0)
            return false;
    return true;

}

int find_first_lit (list<list<int>> formula) {
    for(auto& clause: formula)
        for(auto& lit: clause)
            if(lit!=0)
                return lit;
}

int find_most_popular_lit(list<list<int>> formula) {

    int maxi = -1, lit=0;
    for(int i=1;i<=variables;i++) {
        if(var_app[i] > maxi || var_app[(-1)*i] > maxi) {
            maxi = var_app[i];
            lit = i;
        }
    }
    return lit;
}

bool dpll(list<list <int>> formula, list<int> assignment) {


    int literal =0;
    while(literal = find_unit_clause(formula)) {
        assignment.push_back(literal);
        formula = unit_propagate(formula, literal);
        //g<<"Unit propagation on "<<literal<<'\n';
        //print(formula);
        if(empty_clause(formula)) {
            return false;
        }
    }
    while(literal = find_pure_literal(formula)) {
        assignment.push_back(literal);
        formula = pure_literal(formula, literal);
        //g<<"Pure literal "<<literal<<'\n';
        //print(formula);
        if(empty_clause(formula)){
            return false;
        }
    }

    if(empty_formula(formula)) {
        g<<"SAT\n";
        print_assignment(assignment);
        return true;
    }

    literal = find_first_lit(formula);
    //literal = find_most_popular_lit(formula);

    map<int,int> var_app_copy;

    for(int i=1;i<=variables;i++) {
        var_app_copy[i] = var_app[i];
        var_app_copy[(-1)*i] = var_app[(-1)*i];
    }

    list<list<int>> formula1;
    formula1 = formula;
    formula1.push_back({literal, 0});
    //g<<"Split on "<<literal<<'\n';
    if(dpll(formula1, assignment))
        return true;

    for(int i=1;i<=variables;i++) {
        var_app[i] = var_app_copy[i];
        var_app[(-1)*i] = var_app_copy[(-1)*i];
    }

    list<list<int>> formula2;
    formula2 = formula;
    formula2.push_back({(-1)*literal, 0});
    //g<<"Split on "<<(-1)*literal<<'\n';
    if(dpll(formula2, assignment))
        return true;

    for(int i=1;i<=variables;i++) {
        var_app[i] = var_app_copy[i];
        var_app[(-1)*i] = var_app_copy[(-1)*i];
    }


    return false;
}

int main()
{
    list< list<int> > formula;
    read(variables,clauses, formula);
    //print(formula);

    auto start = high_resolution_clock::now();
    if(!dpll(formula, {})) g<<"UNSAT";
    auto stop = high_resolution_clock::now();
    auto duration = duration_cast<microseconds>(stop - start);
    g << "\ntime: " << duration.count() << endl;
    return 0;

}
