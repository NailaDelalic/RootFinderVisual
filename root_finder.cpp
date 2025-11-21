#include <emscripten/emscripten.h>
#include <cmath>
#include <functional>
#include <limits>
#include <stdexcept>
#include <complex>
#include <vector>
#include <algorithm>

using std::function;
using std::fabs;
using std::numeric_limits;
using std::domain_error;
using std::range_error;
using std::logic_error;
using std::sqrt;
using std::isfinite;
using std::swap;
using std::complex;
using std::vector;
using std::pair;
using std::sort;

enum RegulaFalsiMode {Unmodified, Illinois, Slavic, IllinoisSlavic};

// Global function pointer
std::function<double(double)> currentFunction;

// JavaScript callback - must be extern "C" for consistency
extern "C" void jsLogPoint(double x, double y);
extern "C" void jsLogPointLabeled(double x, double y, const char* label);



// TryBracket - same as in NA
template <typename FunType>
bool TryBracket(FunType f, double x0, double &a, double &b, double hinit, double hmax, double lambda) {
    double h = hinit;
    a = x0;
    double f1 = f(a);

    while (fabs(h) < hmax) {
        b = a + h;
        double f2 = f(b);

        while (!std::isfinite(f2)) {
            h /= (2 * (1 + lambda));
            if (fabs(h) <= fabs(a) * numeric_limits<double>::epsilon()) return false;
            
            b = a + h;
            f2 = f(b);
        }

        if (f1 * f2 <= 0) {
            if (a > b) swap(a, b);
            return true;
        }

        h *= lambda;
        a = b;
        f1 = f2;
    }

    return false;
}

template <typename FunType>
bool BracketRoot(FunType f, double x0, double &a, double &b, double hinit = 1e-5, double hmax = 1e10, double lambda = 1.4) {
    if (hinit <= 0 || hmax <= 0 || lambda <= 0) throw domain_error("Invalid parameters");
    
    if (TryBracket(f, x0, a, b, hinit, hmax, lambda)) return true;
    return TryBracket(f, x0, a, b, -hinit, hmax, lambda);
}

template <typename FunType>
double RegulaFalsiSolve(FunType f, double a, double b, RegulaFalsiMode mode = Slavic, double eps = 1e-10, int maxiter = 100) {
    if (eps <= 0 || maxiter <= 0) throw domain_error("Invalid parameters");

    bool slavic = (mode == Slavic || mode == IllinoisSlavic);
    bool illinois = (mode == Illinois || mode == IllinoisSlavic);

    double f1 = f(a);
    double f2 = f(b);
    
    jsLogPointLabeled(a, f1, "a₀");
    jsLogPointLabeled(b, f2, "b₀");

    if (slavic) {
        f1 = f1 / (1 + fabs(f1));
        f2 = f2 / (1 + fabs(f2));
    }

    if (f1 * f2 > 0) throw range_error("Root must be bracketed");
    
    double c = a;
    double cold = b;
    int n = 0;
    
    while (fabs(c - cold) > eps) {
        if (n >= maxiter) throw logic_error("Given accuracy has not achieved");

        cold = c;
        c = (a * f2 - b * f1) / (f2 - f1);
        double f3 = f(c);
        
        char label[32];
        snprintf(label, sizeof(label), "c%d", n+1);
        jsLogPointLabeled(c, f(c), label);
        
        if (slavic) f3 = f3 / (1 + fabs(f3));
        
        if (fabs(f3) <= eps) return c;

        if (f1 * f3 < 0) {
            b = a;
            f2 = f1;
        }
        if (illinois && f1 * f3 >= 0) f2 /= 2;
        
        a = c;
        f1 = f3;
        n++;
    }

    return c;
}

template <typename FunType>
double RiddersSolve(FunType f, double a, double b, double eps = 1e-10, int maxiter = 100){
    if (eps <= 0 || maxiter <= 0) throw domain_error("Invalid parameters");

    double f1 = f(a);
    double f2 = f(b);
    
    jsLogPointLabeled(a, f1, "a₀");
    jsLogPointLabeled(b, f2, "b₀");

    if (f1 * f2 > 0) throw range_error("Root must be bracketed");

    double c = 0;
    int n = 0;

    while(fabs(b-a) > eps){
        if (n >= maxiter) throw logic_error("Given accuracy has not achieved");
        c = (a + b) / 2;
        double f3 = f(c);
        
        char label[32];
        snprintf(label, sizeof(label), "c%d", n+1);
        jsLogPointLabeled(c, f3, label);

        if (fabs(f3) <= eps) return c;

        double d = c + f3*(c - a)*((f1-f2 > 0) ? 1 : -1) / sqrt(f3*f3 - f1*f2);
        double f4 = f(d);
        
        snprintf(label, sizeof(label), "d%d", n+1);
        jsLogPointLabeled(d, f4, label);

        if(fabs(f4) < eps) return d;

        if (f3 * f4 <= 0) {
            a = c;
            b = d;
            f1 = f3;
            f2 = f4;
        } else if (f1 * f4 <= 0) {
            b = d;
            f2 = f4;
        } else {
            a = d;
            f1 = f4;
        }
        n++;
    }
    
    return (a+b)/2;
}

template <typename FunType1, typename FunType2>
double NewtonRaphsonSolve(FunType1 f, FunType2 fprim, double x0, double eps = 1e-10, double damping = 0, int maxiter = 100) {
    if (eps <= 0 || maxiter <= 0 || damping < 0 || damping >= 1) throw domain_error("Invalid parameters");
    
    
   // if (damping == 0) damping = 0.5;
    
    double x = x0;
    double v = f(x);
    double d = fprim(x);
    double dx = numeric_limits<double>::infinity();
    int n = 0;
    
    jsLogPoint(x, v);

    while (fabs(dx) > eps) {
        if (n >= maxiter) throw logic_error("Convergence has not been achieved");
        if (fabs(v) <= eps) return x;

        dx = v / d;
        double w = v;
        v = f(x - dx);
        d = fprim(x - dx);
        
        jsLogPoint(x - dx, v);

        while (fabs(v) > fabs(w) || !std::isfinite(v) || fabs(d) < numeric_limits<double>::epsilon()) {
            dx *= damping;
            v = f(x - dx);
            d = fprim(x - dx);
            jsLogPoint(x - dx, v);
            if (fabs(dx) < eps) throw logic_error("Convergence has not achieved");
        }
        x -= dx;
        n++;
    }

    return x;
}

// EXPORTED WRAPPERS FOR WEBASSEMBLY 
extern "C" {
    
    void jsLogPoint(double x, double y) {
        EM_ASM({
            if (window.logPoint) {
                window.logPoint($0, $1);
            }
        }, x, y);
    }
    
    void jsLogPointLabeled(double x, double y, const char* label) {
        EM_ASM({
            if (window.logPoint) {
                window.logPoint($0, $1, UTF8ToString($2));
            }
        }, x, y, label);
    }
    
    EMSCRIPTEN_KEEPALIVE
    void setFunction(int funcId) {
        switch(funcId) {
            case 0: currentFunction = [](double x) { return x * x - 4.0; }; break;
            case 1: currentFunction = [](double x) { return x * x * x - 2.0 * x - 5.0; }; break;
            case 2: currentFunction = [](double x) { return std::sin(x) - 0.5; }; break;
            case 3: currentFunction = [](double x) { return std::exp(x) - 3.0; }; break;
            case 4: currentFunction = [](double x) { return std::cos(x) - x; }; break;
            default: currentFunction = [](double x) { return x * x - 4.0; };
        }
    }

    EMSCRIPTEN_KEEPALIVE
    double bracketRoot(double x0, double hinit, double hmax, double lambda) {
        try {
            double a, b;
            bool found = BracketRoot(currentFunction, x0, a, b, hinit, hmax, lambda);
            if (found) {
                jsLogPoint(a, currentFunction(a));
                jsLogPoint(b, currentFunction(b));
                return a;
            }
            return NAN;
        } catch (...) {
            return NAN;
        }
    }

    EMSCRIPTEN_KEEPALIVE
    double regulaFalsiUnmodified(double a, double b, double eps, int maxiter) {
        try {
            return RegulaFalsiSolve(currentFunction, a, b, Unmodified, eps, maxiter);
        } catch (...) {
            return NAN;
        }
    }

    EMSCRIPTEN_KEEPALIVE
    double regulaFalsiIllinois(double a, double b, double eps, int maxiter) {
        try {
            return RegulaFalsiSolve(currentFunction, a, b, Illinois, eps, maxiter);
        } catch (...) {
            return NAN;
        }
    }

    EMSCRIPTEN_KEEPALIVE
    double regulaFalsiSlavic(double a, double b, double eps, int maxiter) {
        try {
            return RegulaFalsiSolve(currentFunction, a, b, Slavic, eps, maxiter);
        } catch (...) {
            return NAN;
        }
    }

    EMSCRIPTEN_KEEPALIVE
    double regulaFalsiIllinoisSlavic(double a, double b, double eps, int maxiter) {
        try {
            return RegulaFalsiSolve(currentFunction, a, b, IllinoisSlavic, eps, maxiter);
        } catch (...) {
            return NAN;
        }
    }

    EMSCRIPTEN_KEEPALIVE
    double riddersSolve(double a, double b, double eps, int maxiter) {
        try {
            return RiddersSolve(currentFunction, a, b, eps, maxiter);
        } catch (...) {
            return NAN;
        }
    }

    EMSCRIPTEN_KEEPALIVE
    double newtonRaphsonSolve(double x0, double eps, double damping, int maxiter) {
        try {
            //will modify derivatives, this is just filler
            auto fprim = [](double x) -> double {
                const double h = 1e-7;
                return (currentFunction(x + h) - currentFunction(x - h)) / (2.0 * h);
            };
            return NewtonRaphsonSolve(currentFunction, fprim, x0, eps, damping, maxiter);
        } catch (...) {
            return NAN;
        }
    }


    
    EMSCRIPTEN_KEEPALIVE
    double bisection(double x0, double x1, double tolerance) {
        double a = x0;
        double b = x1;
        int n = 0;
        
        while (fabs(b - a) > tolerance) {
            double c = (a + b) / 2.0;
            double fc = currentFunction(c);
            
            char label[32];
            snprintf(label, sizeof(label), "c%d", n+1);
            jsLogPointLabeled(c, fc, label);
            
            double fa = currentFunction(a);
            if (fa * fc < 0) {
                b = c;
            } else {
                a = c;
            }
            n++;
        }
        
        return (a + b) / 2.0;
    }
    
    EMSCRIPTEN_KEEPALIVE
    double newtonSimple(double x0, double x1, double tolerance) {
        double x = (x0 + x1) / 2.0;
        const double h = 1e-7;
        const int maxIter = 100;
        
        for (int i = 0; i < maxIter; i++) {
            double fx = currentFunction(x);
            
            char label[32];
            snprintf(label, sizeof(label), "x%d", i);
            jsLogPointLabeled(x, fx, label);
            
            if (fabs(fx) < tolerance) {
                break;
            }
            
            double fprime = (currentFunction(x + h) - currentFunction(x - h)) / (2.0 * h);
            
            if (fabs(fprime) < 1e-10) {
                break;
            }
            
            x = x - fx / fprime;
        }
        
        return x;
    }
    
    EMSCRIPTEN_KEEPALIVE
    double secant(double x0, double x1, double tolerance) {
        double xPrev = x0;
        double xCurr = x1;
        const int maxIter = 100;
        
        for (int i = 0; i < maxIter; i++) {
            double fPrev = currentFunction(xPrev);
            double fCurr = currentFunction(xCurr);
            
            char label[32];
            snprintf(label, sizeof(label), "x%d", i);
            jsLogPointLabeled(xCurr, fCurr, label);
            
            if (fabs(fCurr) < tolerance) {
                break;
            }
            
            if (fabs(fCurr - fPrev) < 1e-10) {
                break;
            }
            
            double xNext = xCurr - fCurr * (xCurr - xPrev) / (fCurr - fPrev);
            xPrev = xCurr;
            xCurr = xNext;
        }
        
        return xCurr;
    }
}