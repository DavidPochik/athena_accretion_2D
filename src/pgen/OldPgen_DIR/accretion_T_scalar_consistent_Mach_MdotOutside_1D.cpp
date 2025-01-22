//==============================================================================
// Athena++ astrophysical MHD code
// Copyright(C) 2014 James M. Stone <jmstone@princeton.edu> and other code contributors
// Licensed under the 3-clause BSD License, see LICENSE file for details
//==============================================================================
//! \file accretion.cpp
//  \brief Problem generator for steady-state accretion, developed from a Parker wind model using the QW EoS.
//

#define COMP_DT 1    // Compute hydro time-steps and save to uov

// C/C++ headers
#include <algorithm>  // min, max
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>   // std::numeric_limits<float>::epsilon()
#include <sstream>
#include <string>
// Athena++ headers
#include "../athena.hpp"
#include "../athena_arrays.hpp"
#include "../coordinates/coordinates.hpp"
#include "../eos/eos.hpp"
#include "../field/field.hpp"
#include "../globals.hpp"
#include "../hydro/hydro.hpp"
#include "../mesh/mesh.hpp"
#include "../parameter_input.hpp"
#include "../utils/utils.hpp"
#include "../scalars/scalars.hpp"

// Static Variables
// r=r_PNS equilibrium quantities: inner pressure, inner temperature, inner electron fraction, inner sound speed squared, GZ pressure modifier, Mach number.
static Real T_eq, Ye_eq, dpdd_0, pModify, Mach, Mdot;
// Problem quantities: gravitational mass, inner density, outer density, inner temperature, outer velocity, outer pressure, mass accretion rate, inner radius,
// inverse inner radius squared (qdotQW), Avogadro's number, cutoff temperature (qdotQW), Inner B-field strength, B-field parameter (angle?), rho0 integration start time.
static Real mu, rho_0, rho_f, v_f, p_f, r_0, inv_r2, Na, Tc, B_0, alpha, t_rho0_0;
// EoS quantities: initial Lnu*Enu^2 (qdotQW), initial Lnubar*Enubar^2 (qdotQW), initial perturbation time, final perturbation time,
// perturbation time coefficient, Coeff_nu perturbation parameter (qdotQW), Coeff_nubar perturbation parameter (qdotQW),
// electrion neutrino average energy, electron antineutrino average energy, electron neutrino luminosity, electron antineutrino luminosity,
// floor temperature.
static Real Coeff_nu_0, Coeff_nubar_0, t_L_0, t_L_1, t_coeff, dCoeff_nu, dCoeff_nubar, eps_nue, eps_nueb, L_nue, L_nueb, T_floor;
// Machine epsilon.
static const Real float_eps = std::numeric_limits<Real>::epsilon();
// Number of rows in the IC file
static int rows;
// User-ouput variable (UOV) indices
static int IDT1, IDT2, IDT3, IDT4, IDT5, IDT6, IDT7, IDT8, IDT9, IDT10, IDT11, IDT12;
// IC file logical parameter
static bool use_IC_file;
// Scalar Ye parameters: Ye index in r & s arrays, Ye index in prim & cons arrays, t index for scalar arrays, number of scalars
static int ye_index, t_index, nscalar_size;
// Scalar Ye parameters: inner boundary ye, outer boundary ye, constant inner Ye.
static Real ye_0, ye_f;
// Scalar Ye pointers: electron number density, electron fraction (passed into EoS)
Real* edens;
Real* efrac;
// NR parameters: guess temperature, guess electron fraction, temperature increment, electron fraction increment,
// tolerance, modifier, maximum iterations, derivative tolerance.
static Real tg, tgs, yg, dtg, dyg, tolsNR, toldNR, modsNR, moddNR, maxcsNR, maxcdNR, epsdNR;
// cross section, tolerance for finding tau, tolerance for adjusting rho_0
static Real g_a, delta_np, mcsq, sigma_0, tau_v, tau_epsilon, rho_epsilon;
// The number of cycles that must pass before base density is perturbed
static int nthcycle;
// Optical depth
Real global_tau;
// Final active zone velocity
Real Vr_FinalActiveZone;
// Final Ghozt zone pressure
Real P_GZ;

// Vector Potential
static Real A3(const Real x1, const Real x2, const Real x3) {
  Real a3 = 0.5 * B_0 * r_0 * std::pow(r_0/x1,2) *
    (std::sin(x2)*std::cos(alpha) - std::cos(x2)*std::cos(x3)*std::sin(alpha));
  return a3;
}

static Real A2(const Real x1, const Real x2, const Real x3) {
  Real a2 = -0.5 * B_0 * r_0 * std::pow(r_0/x1,2) * std::sin(x3) * std::sin(alpha);
  return a2;
}

static Real A1(const Real x1, const Real x2, const Real x3) {
  Real a1=0.0;
  return a1;
}

// Estimates Fermi integrals up to n=5 for a given eta parameter.
Real fermi(Real n, Real eta){
  if (n==0) {
    Real fermi = log(1.0 + exp(eta));
    return fermi;
  } else if (n==1) {
    Real a  = exp(-1.0 * fabs(eta));
    Real s  = std::pow(eta,2) / 2.0 + 1.6449341;
    Real ff = a - std::pow(a,2) / 4.0 + std::pow(a,3) / 9.0 - std::pow(a,4) / 16.0 + std::pow(a,5) / 25.0 - std::pow(a,6) / 36.0 + std::pow(a,7) / 49.0;
    if (eta < 0) {
        Real fermi = ff;
        return fermi;
    } else if (eta == 0) {
        Real fermi = s - ff;
        return fermi;
    } else {
        Real fermi = s - ff;
        return fermi;
    }
  } else if (n==2) {
    Real a  = exp(-1.0 * fabs(eta));
    Real s  = std::pow(eta,3) / 3.0 + 3.2898681 * eta;
    Real ff = 2.0 * (a - std::pow(a,2) / 8.0 + std::pow(a,3) / 27.0 - std::pow(a,4) / 64.0 + std::pow(a,5) / 125.0 - std::pow(a,6) / 216.0);
    if (eta<0) {
        Real fermi = ff;
        return fermi;
    } else if (eta==0) {
        Real fermi = s + ff;
        return fermi;
    } else {
        Real fermi = s + ff;
        return fermi;
    }
  } else if (n==3) {
    Real a  = exp(-1.0 * fabs(eta));
    Real s  = std::pow(eta,4) / 4.0 + 4.9348022 * std::pow(eta,2) + 11.351273;
    Real ff = 6.0 * (a - std::pow(a,2) / 16.0 + std::pow(a,3) / 81.0 - std::pow(a,4) / 256.0);
    if (eta<0) {
        Real fermi = ff;
        return fermi;
    } else if (eta==0) {
        Real fermi = s - ff;
        return fermi;
    } else {
        Real fermi = s - ff;
        return fermi;
    }
  } else if (n==4) {
    Real a  = exp(-1.0 * fabs(eta));
    Real s  = std::pow(eta,5) / 5.0 + 6.5797363 * std::pow(eta,3) + 45.457576 * eta;
    Real ff = 24.0 * (a - std::pow(a,2) / 32.0 + std::pow(a,3) / 243.0);
    if (eta<0) {
        Real fermi = ff;
        return fermi;
    } else if (eta==0) {
        Real fermi = s + ff;
        return fermi;
    } else {
        Real fermi = s + ff;
        return fermi;
    }
  } else if (n==5) {
    Real a  = exp(-1.0 * fabs(eta));
    Real s  = std::pow(eta,6) / 6.0 + 8.2246703 * std::pow(eta,4) + 113.64394 * std::pow(eta,2) + 236.53226;
    Real ff = 120.0 * (a - std::pow(a,2) / 64.0 + std::pow(a,3) / 729.0);
    if(eta<0) {
        Real fermi = ff;
        return fermi;
    } else if(eta==0) {
        Real fermi = s - ff;
        return fermi;
    } else {
        Real fermi = s - ff;
        return fermi;
    }
  } else {
      std::cout << " (accretion.cpp) \n n for fermi_approx wasnt between 0 and 5. \n Something might not be correct";
      return 0.0;
  }
}

// Finds the QW EoS electron chemical potential.
Real QWEta(Real rho, Real T, Real Ye) {
  // Returns eta = mu_e / kbT
  // Physical constants
  Real third         = 1.0 / 3.0;
  Real c             = 2.99792458e10;              // Speed of light in cm/s
  Real k             = 1.380649e-16;               // Boltzmann constant in erg/K
  Real mn            = 1.6726e-24;                 // Baryon mass in g
  Real hbar          = 6.62607015e-27/(2.0*PI);    // Reduced Planck's constant in MeV s
  Real c3            = std::pow(k/(hbar*c),3);
  Real eta_den_const = std::pow(6.0,2.0*third);
  Real root3         = std::sqrt(3.0);
  Real eta_den_A     = std::pow(2.0,third) / eta_den_const;
  Real eta_den_B     = 2.0*std::pow(3.0,third)/eta_den_const;

  Real vol       = mn/rho;
  Real T3        = T*T*T;
  Real T4        = T*T3;
  Real a         = c3*std::pow(T,3)*vol*(PI/3.0);
  Real a2        = SQR(a);
  Real a4        = SQR(a2);
  Real a6        = a2 * a4;
  Real y2        = SQR(Ye);
  Real b         = std::sqrt(4.0*a6+27.0*a4*y2);
  Real term      = std::pow(9.0*a2*Ye+root3*b, third);
  Real eta_by_pi = (eta_den_A)*term/a - (eta_den_B)*a/term; // actually eta/pi
  Real eta       = eta_by_pi * PI;
  return eta;
}

// Qian & Woosley (1996) Heating/cooling function
Real qdotQW(Real temp, Real x, Real ye, Real time) {
  // temp is in MeV
  // returns heating - cooling in units of MeV s^{-1} g^{-1} units
  // smoothly transition from 0 at t<=t_L_0 to 1 at t>=t_L_1
  Real f           = (time <= t_L_0) ? 0.0 :
                    ((time >= t_L_1) ? 1.0 : SQR(std::sin((time - t_L_0) * t_coeff)));
  Real Coeff_nu    = Coeff_nu_0 + f * dCoeff_nu;
  Real Coeff_nubar = Coeff_nubar_0 + f * dCoeff_nubar;
  // Heating; multiplied 1e12 becasue r is units of 1e6 cm (see Qian and Woosely (1996))
  Real out = 1e12*9.65*Na*((1.0-ye)*Coeff_nu + ye*Coeff_nubar)*(1.0-x)*inv_r2;
  out     -= 2.27*Na*std::pow(temp,6); // cooling
  if(temp<Tc) {
    out *= std::exp(-0.5/temp); //alpha particles turnoff heating term for T<0.5 MeV
  }
//  if(temp>Th){
//    out *= std::exp(-tau);
//  }
  return out;
}

Real YeTejas(Real temp, Real ye, Real x, Real Rho) {
  // Returns Sources for Yedot=vdYe/dr in s^-1 units
  // Temperature argument is in MeV
  // Define constants
  Real alpha    = 1.26;                                // Coupling Coefficient
  Real G_F      = 1.16637e-11;                         // Fermi Constant in MeV^-2
  Real Delta    = 1.2935;                              // neutron-proton mass difference in MeV
  Real hbar     = 6.582119569e-22;                     // Planck's constant in MeV s
  Real c        = 2.99792458e10;                       // Light speed in cm/s
  Real erg2MeV  = 6.24151e5;                           // convert erg to MeV
  //Luminosity and epsilon
  Real lnu_y      = L_nue;
  Real epsnu_y    = eps_nue;
  Real lnubar_y   = L_nueb;
  Real epsnubar_y = eps_nueb;
//  if (time<t_L_0) {
//      lnu_y=L_nu;
//      lnubar_y=L_nubar;
//      epsnu_y=eps_nu;
//      epsnubar_y=eps_nubar;
//  }
//  if (time>=t_L_0 && time<=t_L_1) {
//      //Coeff_nu = Coeff_nu_0*std::pow(t_L_0/time,0.92400069*1.5);
//      //Coeff_nubar = Coeff_nubar_0*std::pow(t_L_0/time,0.92400069*1.5);
//      if(time<=3.417921) {
//        lnu_y = L_nu*std::pow((t_L_0-0.399081)/(time-0.399081),0.56185246);
//        lnubar_y = L_nubar*std::pow((t_L_0-0.399081)/(time-0.399081),0.56185246);
//        epsnubar_y=eps_nubar;
//        epsnu_y=eps_nu;
//        //Coeff_nu = Coeff_nu_0*std::pow((t_L_0-0.399991)/(time-0.399991),0.49249801);
//        //Coeff_nubar = Coeff_nubar_0*std::pow((t_L_0-0.399991)/(time-0.399991),0.49249801);
//        //Coeff_nu = Coeff_nu_0*std::pow((t_L_0-0.399235)/(time-0.399235),0.53742558);
//        //Coeff_nubar = Coeff_nubar_0*std::pow((t_L_0-0.399235)/(time-0.399235),0.53742558);
//      }
//      else {
//        lnu_y = L_nu*std::pow((3.01884)/(time-0.399081),1.25488708)*std::pow((t_L_0-0.399081)/(3.417921-0.399081),0.56185246);
//        lnubar_y = L_nubar*std::pow((3.01884)/(time-0.399081),1.25488708)*std::pow((t_L_0-0.399081)/(3.417921-0.399081),0.56185246);
//        epsnu_y = eps_nu*std::pow((3.01884)/(time-0.399081),0.24975336);
//        epsnubar_y = eps_nubar*std::pow((3.01884)/(time-0.399081),0.24975336);
//      }
//  }
//  if (time>t_L_1) {
//      lnu_y=L_nu_f;
//      lnubar_y=L_nubar_f;
//      epsnu_y=eps_nu_f;
//      epsnubar_y=eps_nubar_f;
//  }

  Real ferm5 = fermi(5,0); //118.266;
  Real ferm4 = fermi(4,0); //23.3309;
  Real ferm3 = fermi(3,0); //5.6822;
  Real ferm2 = fermi(2,0); //1.80309;

  Real ktemp_nubar = epsnubar_y  * ferm2 / ferm3;
  Real eavg1_nubar = ktemp_nubar * ferm3 / ferm2;
  Real eavg2_nubar = ktemp_nubar * ktemp_nubar * ferm4 / ferm2;

  Real ktemp_nu = epsnu_y  * ferm2 / ferm3;
  Real eavg1_nu = ktemp_nu * ferm3 / ferm2;
  Real eavg2_nu = ktemp_nu * ktemp_nu * ferm4 / ferm2;

  Real lambda_nue_n  = std::pow(hbar*c,2.0)*(1.0+3.0*alpha*alpha)/(2*PI*PI)*G_F*G_F*lnu_y*1e51*erg2MeV/(r_0*r_0)
                      *(eavg2_nu/eavg1_nu+2.0*Delta+Delta*Delta/eavg1_nu)*(1.0-x); // s^-1 units
  Real lambda_nuebar_p  = std::pow(hbar*c,2.0)*(1.0+3.0*alpha*alpha)/(2*PI*PI)*G_F*G_F*lnubar_y*1e51*erg2MeV/(r_0*r_0)
                      *(eavg2_nubar/eavg1_nubar-2.0*Delta+Delta*Delta/eavg1_nubar)*(1.0-x); // s^-1 units

// Calculate Eta, send in T in K
  Real Eta = QWEta(Rho,temp/8.6173e-11,ye);

  // Reverse reaction rates
  Real f4_0         = fermi(4,0.0);
  Real f4_eta       = fermi(4,Eta);
  Real f4_negeta    = fermi(4,-1.0*Eta);
  Real lambda_ele_p = 0.448*std::pow(temp,5.0)*f4_eta/f4_0;    // s^-1 units (e- p)
  Real lambda_pos_n = 0.448*std::pow(temp,5.0)*f4_negeta/f4_0; // s^-1 units (e+ n)

  // Source term
  //std::cout<<"ENTER YeSOurce   "<<L_nu<<"    "<<eps_nu<<"    "<<lambda_nue_n<<"   "<<lambda_pos_n<<"    "<<lambda_ele_p<<"   "<<lambda_nuebar_p<<"    "<<temp/8.6173e-11<<"    "<<ye<<"    "<<Rho<<"\n";
  return lambda_nue_n+lambda_pos_n-(lambda_nue_n+lambda_pos_n+lambda_nuebar_p+lambda_ele_p)*ye;

}


Real YeSource_QW_Modified(Real Rho, Real T, Real Ye, Real x, Real r) {
  // T is in MeV
  // Returns source term for Yedot from QW 1996
  Real kbol_MeV   = 8.61733326e-11;                               // Boltzmann constant in MeV / K
  Real sigma_0    = 1.76e-44;                                     // Weak interaction cross section in cm^2, taken from Scheck et al 2006
  Real alpha      = 1.26;                                         // Axial coupling coefficient used in QW 1996
  Real G_F        = 1.1663787e-5 * std::pow(1.0e3,-2);            // Fermi Constant in MeV^-2
  Real mn         = 1.0 / Na;                                     // Baryon mass in g
  Real E_e        = 0.511;                                        // Electrn energy in MeV
  Real h          = 4.1356677e-21;                                // Planck's constant in MeV s
  Real hbar       = h / (2.0 * PI);                               // Reduced Planck's constant in MeV s
  Real Delta      = 1.293;                                        // Proton-neutron mass difference in MeV
  Real c          = 2.99792458e10;                                // Speed of light in cm/s
  Real kbT_nue    = eps_nue  * fermi(2,0.0) / fermi(3,0.0);       // Electron neutrino temperature in MeV
  Real kbT_nueb   = eps_nueb * fermi(2,0.0) / fermi(3,0.0);       // Electron antineutrino temperature in MeV
  Real erg2MeV    = 6.24151e5;                                    // convert erg to MeV
  Real prefactor1 = std::pow(hbar * c,2.0) * (1.0 + 3.0 * std::pow(alpha,2.0)) * std::pow(G_F,2.0) * (L_nue  * 1.0e51 * erg2MeV) /
                   (2.0 * std::pow(PI,2.0) * std::pow(r_0,2.0));  // Forward reaction prefactor in MeV^-1 s^-1 units
  Real prefactor  = sigma_0 * PI * (1.0 + 3.0 * std::pow(alpha,2.0)) * c /
                    (std::pow(E_e,2.0) * std::pow(h * c,3.0));    // Reverse reaction prefactor in MeV^-5 s^-1 units

  // Calulate eta_e, send T in K
  Real eta_e = QWEta(Rho,T/kbol_MeV,Ye);
  Real F4_e  = fermi(4.0,eta_e);

  // Calculate energy moments, let eta_nu = 0
  Real e_nue         = kbT_nue                 * fermi(4.0,0.0) / fermi(3.0,0.0); // <eps_nue^2> / <eps_nue>, MeV
  Real one_over_Enue = std::pow(kbT_nue,-1.0)  * fermi(2.0,0.0) / fermi(3.0,0.0); // Inverse of first energy moment, MeV^-1

  // Lambda terms in s^-1
  Real lambda_nue_n  = prefactor1 * (e_nue  + 2.0 * Delta + std::pow(Delta,2.0) * one_over_Enue)  * (1.0 - x);
  Real lambda_pos_n  = prefactor * std::pow(T,5.0) * F4_e;

  // Source term from QW 1996 in s^-1
  Real Source = lambda_nue_n + lambda_pos_n;
//  if(r<30.2e5) {
//    std::cout << "--SOURCE------------------------------" << std::endl;
//    std::cout << "Source       = " << Source       << " s^-1" << std::endl;
//    std::cout << "x            = " << x            << std::endl;
//    std::cout << "lambda_nue_n = " << lambda_nue_n << " s^-1" << std::endl;
//    std::cout << "lambda_pos_n = " << lambda_pos_n << " s^-1" << std::endl;
//    std::cout << "eta_e        = " << eta_e        << std::endl;
//    std::cout << "F4_e         = " << F4_e         << std::endl;
//    std::cout << "T            = " << T            << " MeV" << std::endl;
//    std::cout << "Ye           = " << Ye           << std::endl;
//    std::cout << "r            = " << r            << " cm" << std::endl;
//    std::cout << "--------------------------------------" << std::endl;
//  }
  return Source;
}

Real YeSink_QW_Modified(Real Rho, Real T, Real Ye, Real x, Real r) {
  // T is in MeV
  // Returns sink term for Yedot from QW 1996
  Real kbol_MeV   = 8.61733326e-11;                               // Boltzmann constant in MeV / K
  Real sigma_0    = 1.76e-44;                                     // Weak interaction cross section in cm^2, taken from Scheck et al 2006
  Real alpha      = 1.26;                                         // Axial coupling coefficient used in QW 1996
  Real G_F        = 1.1663787e-5 * std::pow(1.0e3,-2);            // Fermi Constant in MeV^-2
  Real mn         = 1.0 / Na;                                     // Baryon mass in g
  Real E_e        = 0.511;                                        // Electron rest-mass energy in MeV
  Real h          = 4.1356677e-21;                                // Planck's constant in MeV s
  Real hbar       = h / (2.0 * PI);                               // Reduced Planck's constant in MeV s
  Real Delta      = 1.293;                                        // Proton-neutron mass difference in MeV
  Real c          = 2.99792458e10;                                // Speed of light in cm/s
  Real kbT_nue    = eps_nue  * fermi(2,0.0) / fermi(3,0.0);       // Electron neutrino temperature in MeV
  Real kbT_nueb   = eps_nueb * fermi(2,0.0) / fermi(3,0.0);       // Electron antineutrino temperature in MeV
  Real erg2MeV    = 6.24151e5;                                    // convert erg to MeV
  Real prefactor1 = std::pow(hbar * c,2.0) * (1.0 + 3.0 * std::pow(alpha,2.0)) * std::pow(G_F,2.0) * (L_nue  * 1.0e51 * erg2MeV) /
                   (2.0 * std::pow(PI,2.0) * std::pow(r_0,2.0));  // Forward reaction prefactor in MeV^-1 s^-1 units
  Real prefactor2 = std::pow(hbar * c,2.0) * (1.0 + 3.0 * std::pow(alpha,2.0)) * std::pow(G_F,2.0) * (L_nueb * 1.0e51 * erg2MeV) /
                   (2.0 * std::pow(PI,2.0) * std::pow(r_0,2.0));  // Forward reaction prefactor in MeV^-1 s^-1 units
  Real prefactor  = sigma_0 * PI * (1.0 + 3.0 * std::pow(alpha,2.0)) * c /
                    (std::pow(E_e,2.0) * std::pow(h * c,3.0));    // Reverse reaction prefactor in MeV^-5 s^-1 units

  // Calculate eta_e, send T in K
  Real eta_e = QWEta(Rho,T/kbol_MeV,Ye);
  Real F4_e  = fermi(4.0,eta_e);
  Real F4_p  = fermi(4.0,-1.0*eta_e);

  // Calculate energy moments, let eta_nu = 0
  Real e_nue          = kbT_nue                 * fermi(4.0,0.0) / fermi(3.0,0.0); // <eps_nue^2>  / <eps_nue>, MeV
  Real e_nueb         = kbT_nueb                * fermi(4.0,0.0) / fermi(3.0,0.0); // <eps_nueb^2> / <eps_nueb>, MeV
  Real one_over_Enue  = std::pow(kbT_nue,-1.0)  * fermi(2.0,0.0) / fermi(3.0,0.0); // Inverse of first energy moment, MeV^-1
  Real one_over_Enueb = std::pow(kbT_nueb,-1.0) * fermi(2.0,0.0) / fermi(3.0,0.0); // Inverse of first energy moment, MeV^-1

  // Lambda terms in s^-1
  Real lambda_nue_n  = prefactor1 * (e_nue  + 2.0 * Delta + std::pow(Delta,2.0) * one_over_Enue)  * (1.0 - x);
  Real lambda_nueb_p = prefactor2 * (e_nueb + 2.0 * Delta + std::pow(Delta,2.0) * one_over_Enueb) * (1.0 - x);
  Real lambda_pos_n  = prefactor * std::pow(T,5.0) * F4_e;
  Real lambda_ele_p  = prefactor * std::pow(T,5.0) * F4_p;

  // Sink term from QW 1996 in s^-1
  Real Sink = Ye * (lambda_nue_n + lambda_pos_n + lambda_nueb_p + lambda_ele_p);
//  if(r<30.2e5) {
//    std::cout << "--SINK------------------------------" << std::endl;
//    std::cout << "Sink          = " << Sink << " s^-1" << std::endl;
//    std::cout << "x             = " << x    << std::endl;
//    std::cout << "lambda_nue_n  = " << lambda_nue_n  << " s^-1" << std::endl;
//    std::cout << "lambda_pos_n  = " << lambda_pos_n  << " s^-1" << std::endl;
//    std::cout << "lambda_nueb_p = " << lambda_nueb_p << " s^-1" << std::endl;
//    std::cout << "lambda_ele_p  = " << lambda_ele_p  << " s^-1" << std::endl;
//    std::cout << "eta_e         = " << eta_e        << std::endl;
//    std::cout << "F4_e          = " << F4_e         << std::endl;
//    std::cout << "T             = " << T            << " MeV" << std::endl;
//    std::cout << "Ye            = " << Ye           << std::endl;
//    std::cout << "r            = " << r            << " cm" << std::endl;
//    std::cout << "--------------------------------------" << std::endl;
//  }
  return Sink;
}


// Ye source function for scalar Ye (Scheck et al. 2006)
Real YeSourceHEOS(Real temp, Real ye, Real rho, Real r){
  // Returns YeDot_source in s^-1 units
  // Temperature argument is in MeV
  // Define constants
  Real alpha    = 1.26;                                                                                 // Coupling Coefficient
  Real Delta    = 1.293;                                                                                // neutron-proton mass difference in MeV
  Real mn       = 1.6749286e-24;                                                                        // baryon mass in g
  Real me       = 9.1093897e-28;                                                                        // electron mass in g
  Real hbar     = 6.582119569e-22;                                                                      // Planck's constant in MeV s
  Real c        = 2.99792458e10;                                                                        // Light speed in cm/s
  Real erg2MeV  = 6.24151e5;                                                                            // convert erg to MeV
  Real MeV2erg  = 1.6021773e-6;                                                                         // convert MeV to erg
  Real kbol_MeV = 8.61733326e-11;                                                                       // Boltzmann constant in MeV / K
  Real kbol_erg = 1.3806504e-16;                                                                        // Boltzmann constant erg / K
  Real sigma_0  = 1.76e-44;                                                                             // weak cross section in cm^2
  Real sigma    = 1.0 / 4.0 * (3.0 * std::pow(alpha,2) + 1) * sigma_0 / std::pow(me * std::pow(c,2),2); // cm^2 / erg^2

  // Eta_e parameters
  Real fnu    = 0.5 * (1.0 + std::pow(1.0 - std::pow(r_0 / r,2),0.5));           // unitless
  Real Tprime = temp / (hbar * c);                                               // cm^-1
  Real Terg   = temp * MeV2erg;                                                  // erg
  Real tfact  = std::pow(27.0 * ye * rho + std::pow(3.0,0.5) * std::pow(4.0 * std::pow(PI,2) * std::pow(mn,2) * std::pow(Tprime,6) +
                         243.0 * std::pow(ye,2) * std::pow(rho,2),0.5),1.0/3.0); // g^(1/3) cm^-1

  // Electron chemical potential
  Real eta_e = std::pow(12.0 * PI,1.0/3.0) * (std::pow(PI * mn,1.0/3.0) * std::pow(tfact,2) -
                        PI * std::pow(Tprime,2) * mn * std::pow(12.0,1.0/3.0)) / (6.0 * std::pow(mn,2.0/3.0) * tfact * Tprime); // unitless

  // Composition densities (n_e and n_pos are given by equation D.51, which has a typo and is missing temperature)
  Real nb    = rho / mn;                                                                                     // baryon number density, cm^-3
  Real n_e   = 8.0 * PI / std::pow(hbar * 2.0 * PI * c,3) * std::pow(temp,3) * fermi(2,eta_e);        // electron number density, cm^-3
  Real n_pos = 8.0 * PI / std::pow(hbar * 2.0 * PI * c,3) * std::pow(temp,3) * fermi(2,-1.0 * eta_e); // positron number density, cm^-3
  Real n_p   = n_e;                                                                                          // proton number density, cm^-3

  // Neutrino energy moments given by D.42, assume eta_nu = 0
  Real Tnue    = eps_nue  / (kbol_MeV)       * (fermi(2,0) / fermi(3,0));  // K
  Real EpsNue2 = std::pow(Tnue * kbol_erg,2) * (fermi(4,0) / fermi(2,0));  // erg^2
  Real EpsNue1 = Tnue * kbol_erg             * (fermi(3,0) / fermi(2,0));  // erg

  // Positron energy moments given by D.52
  Real EpsPositron2 = std::pow(temp * MeV2erg,2) * (fermi(4,-1.0 * eta_e) / fermi(2,-1.0*eta_e));  // erg^2
  Real EpsPositron1 = temp * MeV2erg             * (fermi(3,-1.0 * eta_e) / fermi(2,-1.0*eta_e));  // erg

  // Reaction rates
  Real lambda_nue_n = sigma * c * (L_nue * std::pow(10,51)) / (4.0 * PI * std::pow(r,2) * c * fnu) * nb *
                                  (EpsNue2 + 2.0 * Delta * MeV2erg * EpsNue1 + std::pow(Delta * MeV2erg,2)) / (EpsNue1); // cm^-3 s^-1
  Real lambda_pos_n = 0.5 * sigma * c * nb * n_pos *
                                  (EpsPositron2 + 2.0 * Delta * MeV2erg * EpsPositron1 * std::pow(Delta * MeV2erg,2));   // cm^-3 s^-1

  // Source term
  Real source = 1.0 / nb * (lambda_nue_n + lambda_pos_n); // s^-1
  return source;

}

// Ye sink function for scalar Ye (Scheck et al. 2006)
Real YeSinkHEOS(Real temp, Real ye, Real rho, Real r){
  // Returns Yedot_sink in s^-1 units
  // Temperature argument is in MeV
  // Define constants
  Real alpha    = 1.26;                                                                             // Coupling Coefficient
  Real Delta    = 1.293;                                                                            // neutron-proton mass difference in MeV
  Real mn       = 1.6749286e-24;                                                                    // baryon mass in g
  Real me       = 9.1093897e-28;                                                                    // electron mass in g
  Real hbar     = 6.582119569e-22;                                                                  // Planck's constant in MeV s
  Real c        = 2.99792458e10;                                                                    // Light speed in cm/s
  Real erg2MeV  = 6.24151e5;                                                                        // convert erg to MeV
  Real MeV2erg  = 1.6021773e-6;                                                                     // convert MeV to erg
  Real kbol_MeV = 8.61733326e-11;                                                                   // Boltzmann constant in MeV / K
  Real kbol_erg = 1.3806504e-16;                                                                    // Boltzmann constant erg / K
  Real sigma_0  = 1.76e-44;                                                                         // weak cross section in cm^2
  Real sigma    = 1.0 / 4.0 * (3.0 * alpha * alpha + 1) * sigma_0 / std::pow(me * std::pow(c,2),2); // cm^2 / erg^2

  // Eta_e parameters
  Real fnu    = 0.5 * (1.0 + std::pow(1.0 - std::pow(r_0 / r,2),0.5));           // unitless
  Real Tprime = temp / (hbar * c);                                               // cm^-1
  Real Terg   = temp * MeV2erg;                                                  // erg
  Real tfact  = std::pow(27.0 * ye * rho + std::pow(3.0,0.5) * std::pow(4.0 * std::pow(PI,2) * std::pow(mn,2) * std::pow(Tprime,6) +
                         243.0 * std::pow(ye,2) * std::pow(rho,2),0.5),1.0/3.0); // g^(1/3) cm^-1

  // Electron chemical potential
  Real eta_e    = std::pow(12.0 * PI,1.0/3.0) * (std::pow(PI * mn,1.0/3.0) * std::pow(tfact,2) -
                           PI * std::pow(Tprime,2) * mn * std::pow(12.0,1.0/3.0)) / (6.0 * std::pow(mn,2.0/3.0) * tfact * Tprime); // unitless

  // Composition densities (n_e and n_pos are given by equation D.51, which has a typo and is missing temperature)
  Real nb    = rho / mn;                                                                                   // baryon number density, cm^-3
  Real n_e   = 8.0 * PI / std::pow(hbar * 2.0 * PI * c,3) * std::pow(temp,3) * fermi(2,eta_e);      // electron number density, cm^-3
  Real n_pos = 8.0 * PI / std::pow(hbar * 2.0 * PI * c,3) * std::pow(temp,3) * fermi(2,-1.0*eta_e); // positron number density, cm^-3
  Real n_p   = n_e;                                                                                        // proton number density, cm^-3

  // Neutrino energy moments given by D.42, assume eta_nu = 0
  Real Tnue    = eps_nue  / (kbol_MeV)       * (fermi(2,0) / fermi(3,0));  // K
  Real EpsNue2 = std::pow(Tnue * kbol_erg,2) * (fermi(4,0) / fermi(2,0));  // erg^2
  Real EpsNue1 = Tnue * kbol_erg             * (fermi(3,0) / fermi(2,0));  // erg

  // Neutrino energy moments given by D.43, assume eta_nu = 0
  Real Tnueb        = eps_nueb  / (kbol_MeV)       * (fermi(2,0) / fermi(3,0));                      // K
  Real EpsNueb2Star = std::pow(Tnueb * kbol_erg,2) * (fermi(4,-1.0 * Delta / Tnueb) / fermi(2,0));  // erg^2
  Real EpsNueb1Star = Tnueb * kbol_erg             * (fermi(3,-1.0 * Delta / Tnueb) / fermi(2,0));  // erg
  Real EpsNueb0Star = 1.0                          * (fermi(2,-1.0 * Delta / Tnueb) / fermi(2,0));  // unitless
  Real EpsNueb1     = Tnueb * kbol_erg             * (fermi(3,0) / fermi(2,0));                      // erg

  // Positron energy moments given by D.52
  Real EpsPositron2 = std::pow(temp * MeV2erg,2) * (fermi(4,-1.0 * eta_e) / fermi(2,-1.0*eta_e));  // erg^2
  Real EpsPositron1 = temp * MeV2erg             * (fermi(3,-1.0 * eta_e) / fermi(2,-1.0*eta_e));  // erg

  // Electron energy moments given by D.53
  Real EpsElectron2Star = std::pow(temp * MeV2erg,2) * (fermi(4,eta_e - Delta/(temp)) / fermi(2,eta_e));  // erg^2
  Real EpsElectron1Star = temp * MeV2erg             * (fermi(3,eta_e - Delta/(temp)) / fermi(2,eta_e));  // erg
  Real EpsElectron0Star = 1.0                        * (fermi(2,eta_e - Delta/(temp)) / fermi(2,eta_e));  // unitless

  // Reactions rates
  Real lambda_nue_n  = sigma * c * (L_nue * std::pow(10,51)) / (4.0 * PI * std::pow(r,2) * c * fnu) * nb *
                      (EpsNue2 + 2.0 * Delta * MeV2erg * EpsNue1 + std::pow(Delta * MeV2erg,2)) / (EpsNue1);                           // cm^-3 s^-1
  Real lambda_pos_n  = 0.5 * sigma * c * nb * n_pos *
                      (EpsPositron2 + 2.0 * Delta * MeV2erg * EpsPositron1 * std::pow(Delta * MeV2erg,2));                             // cm^-3 s^-1
  Real lambda_nueb_p = sigma * c * (L_nueb * std::pow(10,51)) / (4.0 * PI * std::pow(r,2) * c * fnu) * nb *
                      (EpsNueb2Star + 2.0 * Delta * MeV2erg * EpsNueb1Star + std::pow(Delta * MeV2erg,2) * EpsNueb0Star) / (EpsNueb1); // cm^-3 s^-1
  Real lambda_ele_p  = 0.5 * sigma * c * nb * n_e *
                      (EpsElectron2Star + 2.0 * Delta * MeV2erg * EpsElectron1Star + std::pow(Delta * MeV2erg,2) * EpsElectron0Star);  // cm^-3 s^-1

  // Sink term
  Real sink = 1.0 / nb * ye * (lambda_nue_n + lambda_pos_n + lambda_nueb_p + lambda_ele_p); // s^-1
  return sink;
}

// Ye source function for scalar Ye
Real YeSourceQW(Real temp, Real ye, Real x, Real Rho) {
  // Returns Sources for Yedot=vdYe/dr (First part of RHS of equation 7 in Qian & Woosley 1996) in s^-1 units
  // Temperature argument is in MeV
  // Define constants
  Real alpha    = 1.26;                                // Coupling Coefficient
  Real G_F      = 1.1663787e-5 * std::pow(1.0e3,-2);   // Fermi Constant in MeV^-2
  Real Delta    = 1.293;                               // neutron-proton mass difference in MeV
  Real hbar     = 6.582119569e-22;                     // Planck's constant in MeV s
  Real c        = 2.99792458e10;                       // Light speed in cm/s
  Real erg2MeV  = 6.24151e5;                           // convert erg to MeV
  Real kbol_MeV = 8.61733326*std::pow(10,-11);         // Boltzmann constant in MeV / K
  Real lum      = std::pow(10,51);                     // 10^51 erg/s unit

  // Neutrino Energy moments (using Scheck to define these)
  // Neutrino energy moments given by D.42, assume eta_nu = 0
  Real Tnue         = eps_nue  / (kbol_MeV)        * (fermi(2,0)                    / fermi(3,0));  // K
  Real Tnueb        = eps_nueb / (kbol_MeV)        * (fermi(2,0)                    / fermi(3,0));  // K
  Real EpsNue2      = std::pow(Tnue  * kbol_MeV,2) * (fermi(4,0)                    / fermi(2,0));  // MeV^2
  Real EpsNueb2     = std::pow(Tnueb * kbol_MeV,2) * (fermi(4,0)                    / fermi(2,0));  // MeV^2
  Real EpsNueb2Star = std::pow(Tnueb * kbol_MeV,2) * (fermi(4,-1.0 * Delta / Tnueb) / fermi(2,0));  // MeV^2
  Real EpsNue1      = Tnue  * kbol_MeV             * (fermi(3,0)                    / fermi(2,0));  // MeV
  Real EpsNueb1     = Tnueb * kbol_MeV             * (fermi(3,0)                    / fermi(2,0));  // MeV
  Real EpsNueb1Star = Tnueb * kbol_MeV             * (fermi(3,-1.0 * Delta / Tnueb) / fermi(2,0));  // MeV
  Real EpsNueb0Star = 1.0                          * (fermi(2,-1.0 * Delta / Tnueb) / fermi(2,0));  // unitless

  Real e_nue   = EpsNue2  / EpsNue1;  // MeV
  Real e_nueb  = EpsNueb2 / EpsNueb1; // MeV

  // Forward reaction rates
  Real lambda_nue_n  = std::pow(hbar*c,2.0) * (1.0 + 3.0 * alpha * alpha) / (2.0 * PI * PI) * G_F * G_F * L_nue * erg2MeV * lum / (r_0 * r_0)
                      * (e_nue + 2.0 * Delta + Delta * Delta / EpsNue1) * (1.0 - x); // s^-1 units

  // Calculate Eta, send in T in K
  Real Eta = QWEta(Rho,temp/kbol_MeV,ye);

  // Reverse reaction rates
  Real f4_0         = fermi(4.0,0.0);
  Real f4_eta       = fermi(4.0,Eta);
  Real f4_negeta    = fermi(4.0,-1.0*Eta);
  Real lambda_ele_p = 0.448 * std::pow(temp,5.0) * f4_eta    / f4_0; // s^-1 units (e- p)
  Real lambda_pos_n = 0.448 * std::pow(temp,5.0) * f4_negeta / f4_0; // s^-1 units (e+ n)

  // Source term
  Real out = lambda_nue_n+lambda_pos_n;
  return out;
}

// Ye sink function for scalar Ye
Real YeSinkQW(Real temp, Real ye, Real x, Real Rho) {
  // Returns Ye sink for Yedot=v*dYe/dr (equation 7 in Qian & Woosley 1996) in s^-1 units
  // Temperature argument is in MeV
  // Define constants
  Real alpha    = 1.26;                                // Coupling Coefficient
  Real G_F      = 1.1663787e-5 * std::pow(1.0e3,-2); //std::pow(298.2*std::pow(10,3),-2.0); // Fermi Constant in MeV^-2
  Real Delta    = 1.293;                               // neutron-proton mass difference in MeV
  Real hbar     = 6.582119569e-22;                     // Planck's constant in MeV s
  Real c        = 2.99792458e10;                       // Light speed in cm/s
  Real erg2MeV  = 6.24151e5;                           // convert erg to MeV
  Real kbol_MeV = 8.61733326*std::pow(10,-11);         // Boltzmann constant in MeV / K
  Real lum      = std::pow(10,51);                     // 10^51 erg/s unit

  // Neutrino Energy moments (using Scheck to define these)
  // Neutrino energy moments given by D.42, assume eta_nu = 0
  Real Tnue         = eps_nue  / (kbol_MeV)        * (fermi(2,0)                    / fermi(3,0));  // K
  Real Tnueb        = eps_nueb / (kbol_MeV)        * (fermi(2,0)                    / fermi(3,0));  // K
  Real EpsNue2      = std::pow(Tnue  * kbol_MeV,2) * (fermi(4,0)                    / fermi(2,0));  // MeV^2
  Real EpsNueb2     = std::pow(Tnueb * kbol_MeV,2) * (fermi(4,0)                    / fermi(2,0));  // MeV^2
  Real EpsNueb2Star = std::pow(Tnueb * kbol_MeV,2) * (fermi(4,-1.0 * Delta / Tnueb) / fermi(2,0));  // MeV^2
  Real EpsNue1      = Tnue  * kbol_MeV             * (fermi(3,0)                    / fermi(2,0));  // MeV
  Real EpsNueb1     = Tnueb * kbol_MeV             * (fermi(3,0)                    / fermi(2,0));  // MeV
  Real EpsNueb1Star = Tnueb * kbol_MeV             * (fermi(3,-1.0 * Delta / Tnueb) / fermi(2,0));  // MeV
  Real EpsNueb0Star = 1.0                          * (fermi(2,-1.0 * Delta / Tnueb) / fermi(2,0));  // unitless

  Real e_nue   = EpsNue2  / EpsNue1;  // MeV
  Real e_nueb  = EpsNueb2 / EpsNueb1; // MeV

  // Forward reaction rates
  Real lambda_nue_n  = std::pow(hbar*c,2.0) * (1.0 + 3.0 * alpha * alpha) / (2.0 * PI * PI) * G_F * G_F * L_nue  * erg2MeV * lum / (r_0 * r_0)
                      * (e_nue  + 2.0 * Delta + Delta * Delta / EpsNue1)  * (1.0 - x); // s^-1 units
  Real lambda_nueb_p = std::pow(hbar*c,2.0) * (1.0 + 3.0 * alpha * alpha) / (2.0 * PI * PI) * G_F * G_F * L_nueb * erg2MeV * lum / (r_0 * r_0)
                      * (e_nueb - 2.0 * Delta + Delta * Delta / EpsNueb1) * (1.0 - x); // s^-1 units

  // Calculate Eta, send in T in K
  Real Eta = QWEta(Rho,temp/kbol_MeV,ye);

  // Reverse reaction rates
  Real f4_0         = fermi(4.0,0.0);
  Real f4_eta       = fermi(4.0,Eta);
  Real f4_negeta    = fermi(4.0,-1.0*Eta);
  Real lambda_ele_p = 0.448 * std::pow(temp,5.0) * f4_eta    / f4_0; // s^-1 units (e- p)
  Real lambda_pos_n = 0.448 * std::pow(temp,5.0) * f4_negeta / f4_0; // s^-1 units (e+ n)

  // Sink term
  Real out = (lambda_nue_n + lambda_pos_n + lambda_nueb_p + lambda_ele_p) * ye;
  return out;
}

// Calculates the quasi equilibrium (nQSE) condition for Ye (equation 77 in QW1996)
// This function exists mostly for diagnostic purposes.
Real Ye_f(Real temp, Real ye, Real x){
  // Returns Ye_f (equation 77 in Qian & Woosley 1996)
  // Temperature argument is in MeV
  // Define constants
  Real alpha   = 1.26;                                // Coupling Coefficient
  Real G_F     = 1.1663787e-5 * std::pow(1.0e3,-2);   // Fermi Constant in MeV^-2
  Real e_nue   = 1.2 * eps_nue;                       // Electron neutrino energy defined in QW1996 appendix in MeV
  Real e_nueb  = 1.2 * eps_nueb;                      // Electron antineutrino energy defined in QW1996 appendix in MeV
  Real Delta   = 1.293;                               // neutron-proton mass difference in MeV
  Real hbar    = 6.582119569e-22;                     // Planck's constant in MeV s
  Real c       = 2.99792458e10;                       // Light speed in cm/s
  Real erg2MeV = 6.24151e5;                           // convert erg to MeV
  Real lum     = std::pow(10,51);                     // 10^51 erg/s unit

  // Forward reaction rates
  Real lambda_nue_n  = std::pow(hbar*c,2.0)*(1.0+3.0*alpha*alpha)/(2*PI*PI)*G_F*G_F*L_nue*erg2MeV*lum/(r_0*r_0)
                      *(e_nue+2.0*Delta+1.2*Delta*Delta/e_nue)*(1.0-x); // s^-1 units
  Real lambda_nueb_p = std::pow(hbar*c,2.0)*(1.0+3.0*alpha*alpha)/(2*PI*PI)*G_F*G_F*L_nueb*erg2MeV*lum/(r_0*r_0)
                      *(e_nueb-2.0*Delta+1.2*Delta*Delta/e_nueb)*(1.0-x); // s^-1 units

  // Ye_f term
  Real out = (lambda_nue_n) / (lambda_nue_n + lambda_nueb_p);
  return out;
}

Real Heating_QW_Modified(Real x, Real Ye) {
  // returns heating term from QW 1996
  Real sigma_0   = 1.76e-44;                                     // Weak interaction cross section in cm^2, taken from Scheck et al 2006
  Real alpha     = 1.26;                                         // Axial coupling coefficient used in QW 1996
  Real mn        = 1.0 / Na;                                     // Baryon mass in g
  Real E_e       = 0.511;                                        // Electrn energy in MeV
  Real F         = fermi(5,0.0) / fermi(3,0.0);                  // Fermi factors from neutrino energy moments
  Real kbT_nue   = eps_nue  * fermi(2,0.0) / fermi(3,0.0);       // Electron neutrino temperature in MeV
  Real kbT_nueb  = eps_nueb * fermi(2,0.0) / fermi(3,0.0);       // Electron antineutrino temperature in MeV
  Real erg2MeV   = 6.24151e5;                                    // convert erg to MeV
  Real MeV2erg   = 1.60218e-6;                                   // convert MeV to erg
//  Real prefactor = sigma_0 * (1.0 + 3.0 * std::pow(alpha,2.0)) * (1.0e51) /
//                   (8.0 * PI * mn * std::pow(E_e,2.0) * 1.0e12); // Heating prefactor in erg s^-1 g^-1
  Real prefactor = 9.65 * Na * 1.0e12;                           // QW heating prefactor, Rnu is in units of 10^6 cm
  Real Xn        = 1.0 - Ye;                                     // Neutron fraction
  Real Xp        = Ye;                                           // Proton fraction

  // Heating term in erg s^-1 g^-1, L_nue and L_nueb are in 10^51 erg/s units
 // Real H = prefactor * F * (Xn * L_nue * std::pow(kbT_nue,2.0) + Xp * L_nueb * std::pow(kbT_nueb,2.0)) * (1.0 - x) / std::pow(r_0/1.0e6,2.0);
  Real H = MeV2erg * prefactor * F * (Xn * L_nue * std::pow(kbT_nue,2.0) + Xp * L_nueb * std::pow(kbT_nueb,2.0)) * (1.0 - x) / std::pow(r_0,2.0); // erg/s/g
  return H;
}

Real Cooling_QW_Modified(Real Rho, Real T, Real Ye) {
  // T is in MeV
  // Returns cooling term from QW 1996
  Real kbol_MeV  = 8.61733326e-11;                               // Boltzmann constant in MeV / K
  Real sigma_0   = 1.76e-44;                                     // Weak interaction cross section in cm^2, taken from Scheck et al 2006
  Real alpha     = 1.26;                                         // Axial coupling coefficient used in QW 1996
  Real mn        = 1.0 / Na;                                     // Baryon mass in g
  Real E_e       = 0.511;                                        // Electrn energy in MeV
  Real h         = 4.1356677e-21;                                // Planck's constant in MeV s
  Real c         = 2.99792458e10;                                // Speed of light in cm/s
  Real prefactor = sigma_0 * (1.0 + 3.0 * std::pow(alpha,2.0)) * PI * c /
                  (std::pow(E_e,2.0) * mn * pow(h * c,3.0));     // Cooling prefactor in MeV^-5 s^-1 g^-1
  Real MeV2erg   = 1.60218e-6;                                   // convert MeV to erg
  Real Xn        = 1.0 - Ye;                                     // Neutron fraction
  Real Xp        = Ye;                                           // Proton fraction

  // Calculate Eta, send in T in K
  Real eta_e = QWEta(Rho,T/kbol_MeV,Ye);
//  std::cout << "fermi(5,eta_e) = " << fermi(5.0,eta_e) << std::endl;
//  std::cout << "fermi(5,0)   = " << fermi(5,0) << std::endl;

  // Cooling term in is erg s^-1 g^-1
//  Real C = MeV2erg * prefactor * std::pow(T,6.0) * (Xn * fermi(5,eta_e) + Xp * fermi(5,-1.0 * eta_e));
  Real C = MeV2erg * 2.27 * Na / fermi(5,0) * std::pow(T,6.0) * (Xp * fermi(5.0,eta_e) + Xn * fermi(5.0, -1.0 * eta_e)); // erg/s/g;
  return C;
}

Real X_nucleon(Real rho, Real T) {
  // Temperature argument is in MeV
  Real rho_8    = rho / 1.0e8;    // Mass density in 10^8 g/cm^3
  Real xn       = 828.0 * std::pow(T,9.0/8.0) / std::pow(rho_8,3.0/4.0) * std::exp(-7.074 / T); // Free nucleon mass fraction
  return xn;
}

// Electron-type neutrino heating term from Scheck et al. 2006 (equations D.61+D.62)
// Adapted to match Pejcha & Thompson (2012) formalism
Real qdotScheck_H(Real ye, Real r) {
  // Returns heating in units of erg s^{-1} g^{-1} units
  // Physical constants:
  const double c           = 2.99792458*std::pow(10,10); // cm / s
  const double mn          = 1.6749286*std::pow(10,-24); // g
  const double MeV2erg     = 1.6021773*std::pow(10,-6);  // convert MeV to erg
  const double melectron   = 9.1093897*std::pow(10,-28); // g
  const double delta       = 1.2935;                     // MeV
  const double fermi2      = fermi(2,0.0);
  const double fermi4      = fermi(4,0.0);
  const double fermi5      = fermi(5,0.0);
  const double fermi3      = fermi(3,0.0);
  const double fermifactor = fermi2 * fermi5 / ( fermi3 * fermi4 );
  const double alpha       = 1.254;
  const double sigmaweak   = 1.76*std::pow(10,-44)*(1.0+3.0*std::pow(alpha,2))/(4.0*std::pow(melectron*c*c,2));   // weak cross section cm^2 / erg^2

  Real Lnu       = L_nue;
  Real fnu       = 0.5 * (1.0 + std::pow(1.0 - std::pow(r_0 / r,2),0.5));
  Real sinkconst = sigmaweak * 0.5 * (Lnu * std::pow(10,51)) / (4.0 * PI * std::pow(r,2) * fnu); // erg^-1 s^-1

  // --- Absorption Term ---
  Real q_abs  = sinkconst / mn * ((1.0 - ye) * (std::pow(eps_nue * MeV2erg,2) * fermifactor +
                                   2.0 * delta * MeV2erg * eps_nue * MeV2erg * std::pow(fermi(2,0) * fermi(4,0),0.5) / fermi(3,0) +
                                   std::pow(delta * MeV2erg,2)) + ye * (std::pow(eps_nueb * MeV2erg,2) * fermifactor +
                                   3.0 * delta * MeV2erg * eps_nueb * MeV2erg * std::pow(fermi(2,0) * fermi(4,0),0.5) / fermi(3,0) +
                                   3.0 * std::pow(delta * MeV2erg,2))); // erg s^-1 g^-1

  return q_abs;
}

// Electron-type neutrino cooling term from Scheck et al. 2006 (equations D.63+D.64)
// Adapted to match Pejcha & Thompson (2012) formalism
Real qdotScheck_C(Real temp, Real ye, Real rho, Real r) {
  // Returns cooling in units of erg s^{-1} g^{-1} units
  // Temperature argument is in K
  const double c           = 2.99792458*std::pow(10,10);  // cm / s
  const double mn          = 1.6749286*std::pow(10,-24);  // g
  const double MeV2erg     = 1.6021773*std::pow(10,-6);   // convert MeV to erg
  const double melectron   = 9.1093897*std::pow(10,-28);  // g
  const double delta       = 1.2935;                      // MeV
  const double kbol_erg    = 1.3806504*std::pow(10,-16);  // erg / K
  const double hbar        = 1.05457266*std::pow(10,-27); // erg s
  const double alpha       = 1.254;
  const double sigmaweak   = 1.76*std::pow(10,-44)*(1.0+3.0*std::pow(alpha,2))/(4.0*std::pow(melectron*c*c,2));   // weak cross section cm^2 / erg^2

  Real fnu         = 0.5 * (1.0 + std::pow(1.0 - std::pow(r_0 / r,2),0.5));
  Real Tprime      = temp * kbol_erg / (hbar * c); // cm^-1
  Real Terg        = temp * kbol_erg; // erg
  Real tfact       = std::pow(27.0 * ye * rho + std::pow(3.0,0.5) * std::pow(4.0 * std::pow(PI,2) * std::pow(mn,2) * std::pow(Tprime,6) +
                              243.0 * std::pow(ye,2) * std::pow(rho,2),0.5),1.0/3.0); // g^(1/3) cm^-1
  Real eta_e       = std::pow(12.0 * PI,1.0/3.0) * (std::pow(PI * mn,1.0/3.0) * std::pow(tfact,2) -
                              PI * std::pow(Tprime,2) * mn * std::pow(12.0,1.0/3.0)) / (6.0 * std::pow(mn,2.0/3.0) * tfact * Tprime); // unitless
  Real sourceconst = sigmaweak * 0.5 * c * std::pow(Tprime,3) / (std::pow(PI,2) * mn); // erg^-2 s^-1 g^-1

  // --- Emission Term ----
  Real q_em   = sourceconst * (ye * (std::pow(Terg,3) * fermi(5,eta_e - delta * MeV2erg / Terg) +
                              2.0 * delta * MeV2erg * std::pow(Terg,2) * fermi(4,eta_e - delta * MeV2erg / Terg) +
                              std::pow(delta * MeV2erg,2) * Terg * fermi(3,eta_e - delta * MeV2erg / Terg)) +
                              (1.0 - ye) * (std::pow(Terg,3) * fermi(5,-1.0*eta_e) + 3.0 * delta * MeV2erg * std::pow(Terg,2) * fermi(4,-1.0*eta_e) +
                              3.0 * std::pow(delta * MeV2erg,2) * Terg * fermi(3,-1.0*eta_e) + std::pow(delta * MeV2erg,3) * fermi(2,-1.0*eta_e))); // erg s^-1 g^-1

  return q_em;
}

// Free nucleon mass fraction from QW1996 equation 62
Real Xn(Real rho, Real T) {
  // Temperature argument is in MeV
  Real rho_8    = rho / 1.0e8;    // Mass density in 10^8 g/cm^3
  Real xn       = 828.0 * std::pow(T,9.0/8.0) / std::pow(rho_8,3.0/4.0) * std::exp(-7.074 / T); // Free nucleon mass fraction
  return xn;
}

// Temperature at which heating=cooling for Qian & Woosley (1996) qdot
inline Real zeroQ_temp(Real x, Real ye, Real time=0.0) {
  // Smoothly transition from 0 at t<=t_L_0 to 1 at t>=t_L_1
  Real f           = (time <= t_L_0) ? 0.0 :
                    ((time >= t_L_1) ? 1.0 : SQR(std::sin((time - t_L_0) * t_coeff)));
  Real Coeff_nu    = Coeff_nu_0 + f * dCoeff_nu;
  Real Coeff_nubar = Coeff_nubar_0 + f * dCoeff_nubar;
  return std::pow(1e12*9.65/2.27*((1.-ye)*Coeff_nu+ye*Coeff_nubar)*(1.-x)*inv_r2,
                  1./6.) / 8.6173e-11;
}

// Performs double NR procedure to simultaneously determine Ye_0 and T_0 such that Yedot=0 and H-C=0 near the PNS surface, respectively.
// This procedure uses Scheck et al. (2006) qdot (emission and absorption terms) and Yedot (equation D.60).
//void Single_NR(Real Arr[],Real r,Real rho0) {
//  Real x_0      = std::pow(1.0 - std::pow(r_0 / r,2), 0.5); // Equilibrium is being found at r=r_PNS, only needed if using QW heating & sources
//  Real kbol_MeV = 8.61733326*std::pow(10,-11);              // Boltzmann constant in MeV / K
//  Real T0       = tgs;                                      // Set initial guess temperature, K
//  Real Y0       = ye_0;                                     // Surface electron fraction
//
//  for(int i=0; i<=maxcsNR; i++) {
//    // Differential terms
//    Real deltaT0         = dtg*T0;              // K
//    Real dT              = (T0+deltaT0) - (T0); // K
//
//    // Scale terms
//    Real H0         = qdotScheck_H(Y0,r); // erg/s/g
//
//    // Original function
//    Real qdot     = (qdotScheck_H(Y0,r) - qdotScheck_C(T0,Y0,rho0,r));  // erg/s/g
//
//    // Function with differential term
//    Real dqdot_T  = (qdotScheck_H(Y0,r) - qdotScheck_C(T0+deltaT0,Y0,rho0,r));  // erg/s/g
//
//    // Rescale Functions
//    Real f    = qdot     / H0;
//    Real f_dT = dqdot_T  / H0;
//
//    // Define derivative
//    Real dqdotdT = (f_dT - f) / (dT * kbol_MeV);        // MeV^-1
//
//    // Newton-Raphson step
//    Real T1 = T0 - modsNR * f * (1.0 / dqdotdT) / kbol_MeV;      // K
//
//    // Test convergence
//    if(fabs(T1-T0)/fabs(T1)<tolsNR) {
//      Arr[0] = T1;
//      break;
//    } else {
//      T0 = T1;
//    }
//    if(i==maxcsNR){
//      std::cout << "(Newton-Raphson for T) Convergence failed. Returning original guess T..." << std::endl;
//      Arr[0]=T0;
//    }
//  }
//  return;
//}

void Single_NR(Real Arr[], Real r, Real rho0, Real Y0) {
  Real x_0      = std::pow(1.0 - std::pow(r_0 / r,2), 0.5); // Equilibrium is being found at r=r_PNS, only needed if using QW heating & sources
  Real kbol_MeV = 8.61733326*std::pow(10,-11);              // Boltzmann constant in MeV / K
  Real T0       = tgs;                                      // Set initial guess temperature, K
//  Real Y0       = ye_0;                                     // Surface electron fraction
//  Real rho0     = rho_0;

  for(int i=0; i<=maxcsNR; i++) {
    // Differential terms
    Real deltaT0 = dtg*T0;            // K
    Real dT      = (T0+deltaT0) - (T0); // K

    // Scale term
    Real H0 = Heating_QW_Modified(x_0,Y0); // erg/s/g

    // Original function
    Real qdot = Heating_QW_Modified(x_0,Y0) - Cooling_QW_Modified(rho0,T0*kbol_MeV,Y0);  // erg/s/g

    // Function with differential term
    Real dqdot_T = Heating_QW_Modified(x_0,Y0) - Cooling_QW_Modified(rho0,(T0+deltaT0)*kbol_MeV,Y0);  // erg/s/g

    // Rescale Functions
    Real f    = qdot     / H0;
    Real f_dT = dqdot_T  / H0;

    // Define derivative
    Real dqdotdT = (f_dT - f) / (dT * kbol_MeV);        // MeV^-1

    // Newton-Raphson step
    Real T1 = T0 - modsNR * f * (1.0 / dqdotdT) / kbol_MeV;      // K

    // Test convergence
    if(fabs(T1-T0)/fabs(T1)<tolsNR) {
      Arr[0] = T1;
//      Real qdotZero = Heating_QW_Modified(x_0,Y0) - Cooling_QW_Modified(rho0,T1*kbol_MeV,Y0);
//      std::cout << "NR Converged: qdot = " << qdotZero << " erg/s/g" << std::endl;
//      std::cout << " " << std::endl;

//      std::cout << "Common NR W" << std::endl;
//      std::cout << "Teq = " << T1 * kbol_MeV << " MeV" << std::endl;
//      std::cout << "dT increment = " << dtg_s << std::endl;
//      std::cout << "tolerance    = " << tolsNR << std::endl;
//      std::cout << "|T1-T0|/|T1| = " << fabs(T1-T0)/fabs(T1) << std::endl;
      break;
    } else {
//      std::cout << "|T1-T0|/|T1| = " << fabs(T1-T0)/fabs(T1) << std::endl;
//      std::cout << "T0           = " << T0 << " K" << std::endl;
//      std::cout << "T1           = " << T1 << " K" << std::endl;
//      std::cout << "qdot         = " << qdot << " erg/s/g" << std::endl;
      T0 = T1;
    }
    if(i==maxcsNR){
      std::cout << "(Newton-Raphson for T) Convergence failed. Returning final iteration of T..." << std::endl;
      Arr[0]=T0;
    }
  }
  return;
}

void Double_NR(Real Arr[], Real ra, Real rho0) {
  // Returns T_eq and Y_eq as Arr[0] and Arr[1] respectively.
  Real x_0      = std::pow(1.0 - std::pow(r_0 / ra,2), 0.5); // Equilibrium is being found at r=r_PNS, only needed if using QW heating & sources
  Real MeV      = 8.6173e-11;                                // kb in MeV/K
  Real kbol_MeV = 8.61733326*std::pow(10,-11);               // Boltzmann constant in MeV / K
  Real T0       = tg;                                        // Set initial guess temperature
  Real Y0       = yg;                                        // Set initial guess electron fraction
  for(int i=0; i<=maxcdNR; i++){

    // Define differential terms
    Real deltaT0 = dtg*T0;
    Real deltaY0 = dyg*Y0;
    Real dYe     = (Y0+deltaY0) - (Y0);
    Real dT      = (T0+deltaT0) - (T0);

    // Define scale terms
    Real H0         = qdotScheck_H(Y0,ra);
    Real H0_dT      = qdotScheck_H(Y0,ra);
    Real H0_dY      = qdotScheck_H(Y0+deltaY0,ra);
    Real Source0    = YeSourceHEOS(T0*kbol_MeV,Y0,rho0,r_0);
    Real Source0_dT = YeSourceHEOS((T0+deltaT0)*kbol_MeV,Y0,rho0,r_0);
    Real Source0_dY = YeSourceHEOS(T0*kbol_MeV,Y0+deltaY0,rho0,r_0);

    // Define 'original' source functions
    Real qdot    = (qdotScheck_H(Y0,ra) - qdotScheck_C(T0,Y0,rho0,ra));
    Real Yedot   = (YeSourceHEOS(T0*kbol_MeV,Y0,rho0,r_0) - YeSinkHEOS(T0*kbol_MeV,Y0,rho0,r_0));

    // Define source functions with differentials
    Real dqdot_T  = (qdotScheck_H(Y0,ra) - qdotScheck_C(T0+deltaT0,Y0,rho0,ra));
    Real dqdot_Y  = (qdotScheck_H(Y0+deltaY0,ra) - qdotScheck_C(T0,Y0+deltaY0,rho0,ra));
    Real dYedot_T = (YeSourceHEOS((T0+deltaT0)*kbol_MeV,Y0,rho0,r_0) - YeSinkHEOS((T0+deltaT0)*kbol_MeV,Y0,rho0,r_0));
    Real dYedot_Y = (YeSourceHEOS(T0*kbol_MeV,Y0+deltaY0,rho0,r_0) - YeSinkHEOS(T0*kbol_MeV,Y0+deltaY0,rho0,r_0));

    // Define rescaled source functions
    Real f    = qdot     / H0;
    Real g    = Yedot    / Source0;
    Real f_dT = dqdot_T  / H0; //H0_dT;
    Real f_dY = dqdot_Y  / H0; //H0_dY;
    Real g_dT = dYedot_T / Source0; //Source0_dT;
    Real g_dY = dYedot_Y / Source0; //Source0_dY;

    // Define rescaled source function derivatives
    Real dqdotdT = (f_dT - f) / (dT*kbol_MeV);
    Real dqdotdY = (f_dY - f) / (dYe);
    Real dYdotdT = (g_dT - g) / (dT*kbol_MeV);
    Real dYdotdY = (g_dY - g) / (dYe);

    if(fabs(dqdotdT) < epsdNR || fabs(dqdotdY) < epsdNR || fabs(dYdotdT) < epsdNR || fabs(dYdotdY) < epsdNR) {
       std::cout << "One of the derivatives is too small! (Double_NR)" << std::endl;
       std::cout << "Returning guess T and Ye by default." << std::endl;
       std::cout << "dqdotdT = " << dqdotdT << std::endl;
       std::cout << "dqdotdY = " << dqdotdY << std::endl;
       std::cout << "dYdotdT = " << dYdotdT << std::endl;
       std::cout << "dYdotdY = " << dYdotdY << std::endl;
       Arr[0] = T0;
       Arr[1] = Y0;
       break;
    }

    ////////////////////////////////////////////////////
    // Invert Jacobian to find delta terms:           //
    //           A          *   x       =   b         //
    //                                                //
    // [ dqdotdT  dqdotdY ]   [ delT  ]   [ f ]       //
    // [                  ] * [       ] = [   ]       //
    // [ dYdotdT  dYdotdY ]   [ delYe ]   [ g ]       //
    //                                                //
    //                          x       = A^-1 * b    //
    ////////////////////////////////////////////////////

    // Invert matrix A (2x2)
    Real a      = dqdotdT;
    Real b      = dqdotdY;
    Real c      = dYdotdT;
    Real d      = dYdotdY;
    Real detA   = a*d - b*c;
    Real Ainv00 = 1.0/detA * (d);
    Real Ainv01 = 1.0/detA * (-1.0 * b);
    Real Ainv10 = 1.0/detA * (-1.0 * c);
    Real Ainv11 = 1.0/detA * (a);
    Real delT   = (f*Ainv00 + g*Ainv01) / kbol_MeV; // Returns temperature increment in K
    Real delYe  = f*Ainv10 + g*Ainv11;

    // Determine new T and Ye values. Minus sign is a typical NR convention.
    Real T1 = T0 - moddNR * delT;
    Real Y1 = Y0 - moddNR * delYe;

    // Check if T and Ye simultaneously converge. If not, continue iterating.
    if(fabs(T1-T0)/fabs(T1) < toldNR && fabs(Y1-Y0)/fabs(Y1) < toldNR){
        Arr[0] = T1;
        Arr[1] = Y1;
     //   std::cout << "Double NR Success" << std::endl;
        break;
    } else {
      T0 = T1;
      Y0 = Y1;
    }
    if(i==maxcdNR) {
      Arr[0] = tg; //T1;
      Arr[1] = yg; //Y1;
    }
  }
  return;
}

// exists_test1 from https://stackoverflow.com/a/12774387/2275975
inline bool exists (const std::string& name) {
    if (FILE *file = fopen(name.c_str(), "r")) {
        fclose(file);
        return true;
    } else {
        return false;
    }
}

//Heating/cooling source term
void heat_cool(MeshBlock *pmb, const Real time, const Real dt,
               const AthenaArray<Real> &prim, const AthenaArray<Real> &prim_scalar,
               const AthenaArray<Real> &bcc, AthenaArray<Real> &cons,
               AthenaArray<Real> &cons_scalar);

// Boundary Condition
void InflowInnerX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                   FaceField &b, Real time, Real dt, int is, int ie, int js,
                   int je, int ks, int ke, int ngh);
void InflowMdotInnerX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                       FaceField &b, Real time, Real dt, int is, int ie, int js,
                       int je, int ks, int ke, int ngh);
void HSEInnerX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                FaceField &b, Real time, Real dt, int is, int ie, int js,
                int je, int ks, int ke, int ngh);
void HSE2InnerX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                 FaceField &b, Real time, Real dt, int is, int ie, int js,
                 int je, int ks, int ke, int ngh);
void OutflowOuterX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                   FaceField &b, Real time, Real dt, int is, int ie, int js,
                   int je, int ks, int ke, int ngh);
void InflowOuterX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                   FaceField &b, Real time, Real dt, int is, int ie, int js,
                   int je, int ks, int ke, int ngh);

//------------------------------------------------------------------------------
//! \fn void Mesh::InitUserMeshData(ParameterInput *pin)
//  \brief Function to initialize problem-specific data in mesh class.  Can also be used
//  to initialize variables which are global to (and therefore can be passed to) other
//  functions in this file.  Called in Mesh constructor.

void Mesh::InitUserMeshData(ParameterInput *pin) {
  EnrollUserExplicitSourceFunction(heat_cool);
  // set outer BC
  if (pin->GetString("mesh", "ox1_bc").compare("user") == 0) {
    if (Globals::my_rank == 0)
      printf("Using USER outer BC.\n");
    EnrollUserBoundaryFunction(BoundaryFace::outer_x1, InflowOuterX1);
  }
  // set inner BC
  int inner_BC_choice = pin->GetOrAddInteger("problem", "inner_BC_choice", 0);
  if (inner_BC_choice == 0) {
    EnrollUserBoundaryFunction(BoundaryFace::inner_x1, InflowInnerX1);
  } else if (inner_BC_choice == 1) {
    EnrollUserBoundaryFunction(BoundaryFace::inner_x1, InflowMdotInnerX1);
  } else if (inner_BC_choice == 2) {
    EnrollUserBoundaryFunction(BoundaryFace::inner_x1, HSEInnerX1);
  } else if (inner_BC_choice == 3) {
    EnrollUserBoundaryFunction(BoundaryFace::inner_x1, HSE2InnerX1);
  } else {
    std::stringstream msg;
    msg << "### FATAL ERROR in Mesh::InitUserMeshData" << std::endl
        << "Invalid inner BC choice (" << inner_BC_choice << ")." << std::endl;
    ATHENA_ERROR(msg);
  }
  printf("Using USER inner BC %d.\n", inner_BC_choice);

  Real inf     = std::numeric_limits<Real>::infinity();

  // Problem quantities
  mu       = pin->GetReal("problem","GM");
  rho_0    = pin->GetReal("problem","rho_0");
  rho_f    = pin->GetReal("problem","rho_f");
  v_f      = pin->GetReal("problem","v_f");
  p_f      = pin->GetReal("problem","p_f");
  r_0      = pin->GetReal("mesh","x1min");
  inv_r2   = std::pow(r_0, -2);
  Na       = pin->GetReal("problem","Na");
  Tc       = pin->GetReal("problem","T_cutoff");
  B_0      = pin->GetReal("problem","B_0");
  B_0      = B_0/(std::pow(4.0*PI,0.5)); //convert to Lorentz-Heaviside units
  alpha    = pin->GetReal("problem","alpha");
  t_rho0_0 = pin->GetOrAddReal("problem","t_rho0_perturb",inf);
  pModify  = pin->GetOrAddReal("problem","pMod",1.0);
  Mach     = pin->GetOrAddReal("problem","MachNumber",1.0);
  Mdot     = pin->GetReal("problem","mdot");

  // Passive scalar quantities
  ye_index     = pin->GetInteger("hydro","helm_ye_index");
  t_index      = pin->GetInteger("hydro","helm_temp_index");
  nscalar_size = pin->GetInteger("hydro","nsSize");
  ye_f         = pin->GetReal("hydro","Ye_f");
  ye_0         = pin->GetReal("hydro","Ye_0");

  // Quantities used for calculating optical depth
  g_a         = pin->GetReal("problem","Ga");
  delta_np    = pin->GetReal("problem","Delta");
  mcsq        = pin->GetReal("problem","MeCsq");
  sigma_0     = pin->GetReal("problem","Sigma0");
  tau_v       = pin->GetReal("problem","Tau");
  tau_epsilon = pin->GetReal("problem","Tau_Eps");
  rho_epsilon = pin->GetReal("problem","Rho_Eps");
  nthcycle    = pin->GetInteger("problem","ModuloNumber");

  // Single NR parameters
  tgs     = pin->GetReal("problem","Tg_NR");
  dtg     = pin->GetReal("problem","DeltaTg_NR");
  dyg     = pin->GetReal("problem","DeltaYeg_NR");
  tolsNR  = pin->GetReal("problem","Tolerance_NR");
  maxcsNR = pin->GetReal("problem","maxC_NR");
  modsNR  = pin->GetReal("problem","Modifier_NR");

  // Double NR parameters
  tg      = pin->GetReal("problem","Tg_doubleNR");
  yg      = pin->GetReal("problem","Yeg_doubleNR");
  dtg     = pin->GetReal("problem","DeltaTg_doubleNR");
  dyg     = pin->GetReal("problem","DeltaYeg_doubleNR");
  toldNR  = pin->GetReal("problem","Tolerance_doubleNR");
  moddNR  = pin->GetReal("problem","Modifier_doubleNR");
  maxcdNR = pin->GetReal("problem","MaxC_doubleNR");
  epsdNR  = pin->GetReal("problem","eps_doubleNR");

  // final lumonosity/energies
  Real L_nu      = pin->GetReal("problem","L_nu");
  Real L_nubar   = pin->GetReal("problem","L_nubar");
  L_nue          = pin->GetReal("problem","L_nu");
  L_nueb         = pin->GetReal("problem","L_nubar");
  Real eps_nu    = pin->GetReal("problem","eps_nu");
  Real eps_nubar = pin->GetReal("problem","eps_nubar");
  eps_nue        = pin->GetReal("problem","eps_nu");
  eps_nueb       = pin->GetReal("problem","eps_nubar");
  Coeff_nu_0     = L_nu * SQR(eps_nu);
  Coeff_nubar_0  = L_nubar * SQR(eps_nubar);

  // finial lumonosity/energies
  L_nu         = pin->GetOrAddReal("problem","L_nu_f",L_nu);
  L_nubar      = pin->GetOrAddReal("problem","L_nubar_f",L_nubar);
  eps_nu       = pin->GetOrAddReal("problem","eps_nu_f",eps_nu);
  eps_nubar    = pin->GetOrAddReal("problem","eps_nubar_f",eps_nubar);
  Real coeff   = L_nu * SQR(eps_nu);
  dCoeff_nu    = coeff - Coeff_nu_0;
  coeff        = L_nubar * SQR(eps_nubar);
  dCoeff_nubar = coeff - Coeff_nubar_0;
  t_L_0        = pin->GetOrAddReal("problem","l_transition_start",inf);
  t_L_1        = pin->GetOrAddReal("problem","l_transition_end",inf);
  if (t_L_1 < inf && t_L_1 <= t_L_0) {
    std::stringstream msg;
    msg << "### FATAL ERROR in Mesh::InitUserMeshData" << std::endl
        << "l_transition_end <= l_transition_start" << std::endl;
    ATHENA_ERROR(msg);
  }
  t_coeff = 0.5 * PI / (t_L_1 - t_L_0);
  T_floor = pin->GetOrAddReal("hydro", "T_floor", float_eps);

  // Parse IC choice
  std::string file;
  bool has_file = pin->DoesParameterExist("problem", "file");
  if (has_file) {
    file = pin->GetString("problem", "file");
  }
  bool use_IC_specified = pin->DoesParameterExist("problem", "use_IC_file");
  use_IC_file = pin->GetOrAddBoolean("problem", "use_IC_file", has_file);

  if (use_IC_specified && use_IC_file) {
    if (!has_file) {
      std::stringstream msg;
      msg << "### FATAL ERROR in Mesh::InitUserMeshData" << std::endl
          << "No IC file specified in input file." << std::endl;
      ATHENA_ERROR(msg);
    }
    if (!exists(file)) {
      std::stringstream msg;
      msg << "### FATAL ERROR in Mesh::InitUserMeshData" << std::endl
          << "Specified IC file " << file << "does not exits." << std::endl;
      ATHENA_ERROR(msg);
    }
  }

  if (has_file) {
    if (!exists(file)) {
      use_IC_file = false;
      if (Globals::my_rank == 0) {
        std::cout << "Unable to locate IC file " << file << ", reverting to code IC."
                  << std::endl;
      }
    }
  }

  // Read ICs from data file
  if (use_IC_file) {
    rows        = pin->GetInteger("problem", "rows");
    int cols    = pin->GetInteger("problem", "cols");
    int col_rho = pin->GetInteger("problem", "col_rho");
    int col_v   = pin->GetInteger("problem", "col_v");
    int col_T   = pin->GetInteger("problem", "col_T");
    int col_Ye  = pin->GetInteger("problem", "col_Ye");

    // Prepare arrays to hold profile
    AllocateRealUserMeshDataField(11);

    ruser_mesh_data[0].NewAthenaArray(rows);
    ruser_mesh_data[1].NewAthenaArray(rows);
    ruser_mesh_data[2].NewAthenaArray(rows);
    ruser_mesh_data[3].NewAthenaArray(rows);
    ruser_mesh_data[4].NewAthenaArray(rows);
    ruser_mesh_data[5].NewAthenaArray(rows);
    ruser_mesh_data[6].NewAthenaArray(rows);
    ruser_mesh_data[7].NewAthenaArray(rows);
    ruser_mesh_data[8].NewAthenaArray(rows);
    ruser_mesh_data[9].NewAthenaArray(rows);
    AthenaArray<Real>& r_in{ruser_mesh_data[0]};
    AthenaArray<Real>& rho_in{ruser_mesh_data[1]};
    AthenaArray<Real>& v_in{ruser_mesh_data[2]};
    AthenaArray<Real>& T_in{ruser_mesh_data[3]};
    AthenaArray<Real>& Ye_in{ruser_mesh_data[4]};

    // Data structure for calculating optical depth [IS THIS CORRECT? I FEEL LIKE SOMETHING IS OFF HERE]
    AthenaArray<Real>& lsum{ruser_mesh_data[5]};
    AthenaArray<Real>& oldrho{ruser_mesh_data[6]};
    AthenaArray<Real>& Teq{ruser_mesh_data[7]};
    AthenaArray<Real>& PGZ{ruser_mesh_data[8]};

    // Data stucture for tracking cycle number
    AllocateIntUserMeshDataField(1);
    iuser_mesh_data[0].NewAthenaArray(rows);
    AthenaArray<int>& counter{iuser_mesh_data[0]};

    if (Globals::my_rank == 0)
      std::cout<< "Using IC file: " << file << "\n";

    std::string line;
    std::ifstream stream;
    stream.open(file);
    Real s_vals[cols];

    for (int n = 0; n < rows; ++n) {
      std::getline(stream, line);
      std::string word;
      std::stringstream iss(line);
      int m=0;
      while (iss >> word) {
        s_vals[m]=std::stof(word);
        m=m+1;
      }
      r_in(n)   = s_vals[0];
      rho_in(n) = s_vals[col_rho+1];
      v_in(n)   = s_vals[col_v+1];
      T_in(n)   = s_vals[col_T+1];
      Ye_in(n)  = s_vals[col_Ye+1];
    }
  }
  return;
}

void MeshBlock::InitUserMeshBlockData(ParameterInput *pin) {

  if (COMP_DT) {
      int i = 0;

      IDT1 = i;
      IDT2 = i + 1;
      IDT3 = i + 2;
      IDT4 = i + 3;
      IDT5 = i + 4;
      IDT6 = i + 5;
      IDT7 = i + 6;
      IDT8 = i + 7;
      IDT9 = i + 8;
      IDT10 = i + 9;
      IDT11 = i + 10;
      IDT12 = i + 11;
      i += 12;

      AllocateUserOutputVariables(i);

      SetUserOutputVariableName(IDT1, "dt1");
      SetUserOutputVariableName(IDT2, "dt2");
      SetUserOutputVariableName(IDT3, "dt3");
      SetUserOutputVariableName(IDT4, "x1flux");
      SetUserOutputVariableName(IDT5, "dflx_vol");
      SetUserOutputVariableName(IDT6, "coord_src1");
      SetUserOutputVariableName(IDT7, "extra1");
      SetUserOutputVariableName(IDT8, "extra2");
      SetUserOutputVariableName(IDT9, "extra3");
      SetUserOutputVariableName(IDT10, "extra4");
      SetUserOutputVariableName(IDT11, "extra5");
      SetUserOutputVariableName(IDT12, "extra6");

  }
}

//------------------------------------------------------------------------------
//! \fn void MeshBlock::ProblemGenerator(ParameterInput *pin)
//  \brief Problem Generator for the Parker wind

void MeshBlock::ProblemGenerator(ParameterInput *pin) {
  if (use_IC_file) {
    // define references for MeshBlock::ProblemGenerator
    AthenaArray<Real>& r_in{pmy_mesh->ruser_mesh_data[0]};
    AthenaArray<Real>& rho_in{pmy_mesh->ruser_mesh_data[1]};
    AthenaArray<Real>& v_in{pmy_mesh->ruser_mesh_data[2]};
    AthenaArray<Real>& T_in{pmy_mesh->ruser_mesh_data[3]};
    AthenaArray<Real>& Ye_in{pmy_mesh->ruser_mesh_data[4]};

    for (int k=ks; k<=ke; k++) {
      // Real phi = pcoord->x3v(k);
      for (int j=js; j<=je; j++) {
        Real theta = pcoord->x2v(j);
        for (int i=is; i<=ie; i++) {
          Real r  = pcoord->x1v(i);
          Real r0 = 5e6;
          Real mn = 1.6749286e-24;                // baryon mass in g
          Real rho, v, temp, ye;

          int index=0;
          Real min = 1e15;
          Real diff;

          for (int f=0; f<rows; f++) {
            diff = r-r_in(f);
            if(diff>=0.0) {
              if(diff<min) {
                min   = diff;
                index = f;
              }
            }
          }
          //linear interpolation when r values in ICs and simulation are different
          if(r<2.1e6 and rho_0>1.5e12) {
            Real qp = std::pow(r_0/r,20.0);
            rho     = rho_0*qp;
            // Real mdot= 4.0*3.14*r*r*rho_in(index)*v_in(index);
            v = (4.34e-4)*2e33/(4.0*3.14*r*r*rho);
          }
          else {
            rho = rho_in(index)+(r-r_in(index))*(rho_in(index+1)-rho_in(index))
                      /(r_in(index+1)-r_in(index));
            v   = v_in(index)+(r-r_in(index))*(v_in(index+1)-v_in(index))
                    /(r_in(index+1)-r_in(index));
          }

          temp = T_in(index)+(r-r_in(index))*(T_in(index+1)-T_in(index))
                    /(r_in(index+1)-r_in(index));
          ye   = Ye_in(index)+(r-r_in(index))*(Ye_in(index+1)-Ye_in(index))
                    /(r_in(index+1)-r_in(index));

          phydro->u(IDN,k,j,i)        = rho;
          phydro->u(IM1,k,j,i)        = v * rho;
          phydro->u(IM2,k,j,i)        = 0.0;
          phydro->u(IM3,k,j,i)        = 0.0;
          pscalars->s(ye_index,k,j,i) = ye * rho;
          pscalars->s(t_index,k,j,i)  = temp * rho;
          pscalars->r(ye_index,k,j,i) = ye;
          pscalars->r(t_index,k,j,i)  = temp;
          edens                       = &pscalars->s(ye_index,k,j,i);
          efrac                       = &pscalars->r(ye_index,k,j,i);
          Real r_scalar[nscalar_size];
          Real s_scalar[nscalar_size];
          for (int ns=0; ns<nscalar_size; ns++) {
            r_scalar[ns] = pscalars->r(ns,k,j,i);
            s_scalar[ns] = pscalars->s(ns,k,j,i);
          }

          if(std::isnan(pscalars->r(ye_index,k,j,i)) || pscalars->r(ye_index,k,j,i) < 1.0e-4) {
            std::cout << "(ProblemGenerator) Ye is nan or super low in value (0):" << std::endl;
            std::cout << "Ye  = " << pscalars->r(ye_index,k,j,i) << std::endl;
            std::cout << "rho = " << phydro->u(IDN,k,j,i) << " g/cm^3" << std::endl;
            std::cout << "T   = " << temp << " K" << std::endl;
          }
          if(std::isnan(temp)) {
            std::cout << "(ProblemGenerator) temp is nan (1):" << std::endl;
            std::cout << "Ye  = " << pscalars->r(ye_index,k,j,i) << std::endl;
            std::cout << "rho = " << phydro->u(IDN,k,j,i) << " g/cm^3" << std::endl;
            std::cout << "T   = " << temp << " K" << std::endl;
          }
          if(std::isnan(phydro->u(IDN,k,j,i))) {
            std::cout << "(ProblemGenerator) rho is nan (2):" << std::endl;
            std::cout << "Ye  = " << pscalars->r(ye_index,k,j,i) << std::endl;
            std::cout << "rho = " << phydro->u(IDN,k,j,i) << " g/cm^3" << std::endl;
            std::cout << "T   = " << temp << " K" << std::endl;
          }
          if (NON_BAROTROPIC_EOS) {
            if (GENERAL_EOS) {
              Real pressure        = peos->PresFromRhoT(rho, temp, r_scalar);
              phydro->u(IEN,k,j,i) = peos->EgasFromRhoP(rho, pressure, r_scalar);
           //   if(i==ie-1) {
           //     std::cout <<"(ProblemGenerator at i=ie-i): r =  "<< r <<  " cm" << std::endl;
           //     std::cout << "rho    = " << phydro->u(IDN,k,j,i) << " g/cm^3" << std::endl;
           //     std::cout << "Ye     = " << pscalars->r(ye_index,k,j,i) << std::endl;
           //     std::cout << "T      = " << temp << " K" << std::endl;
           //     std::cout << "P      = " << pressure << " erg/cm^3" << std::endl;
           //     std::cout << "u(IPR) = " << phydro->u(IPR,k,j,i) << " erg/cm^3" << std::endl;
           //     std::cout << " " << std::endl;
           //   }
           //   if(i==ie) {
           //     std::cout <<"(ProblemGenerator at i=ie): r =  "<< r <<  " cm" << std::endl;
           //     std::cout << "rho    = " << phydro->u(IDN,k,j,i) << " g/cm^3" << std::endl;
           //     std::cout << "Ye     = " << pscalars->r(ye_index,k,j,i) << std::endl;
           //     std::cout << "T      = " << temp << " K" << std::endl;
           //     std::cout << "P      = " << pressure << " erg/cm^3" << std::endl;
           //     std::cout << "u(IPR) = " << phydro->u(IPR,k,j,i) << " erg/cm^3" << std::endl;
           //     std::cout << " " << std::endl;
           //   }
            }
            phydro->u(IEN,k,j,i) += 0.5 * (SQR(phydro->u(IM1,k,j,i)) + SQR(phydro->u(IM2,k,j,i))
                                        +  SQR(phydro->u(IM3,k,j,i))) / rho;

          }
        }
      }
    }
  }

  if (MAGNETIC_FIELDS_ENABLED) {
    // if root processor and zeroth block
    if ((Globals::my_rank == 0) && (lid == 0)){
      std::cout<<"YES ENTER B field\n";
    }
    AthenaArray<Real> a1,a2,a3;
    int nx1 = (ie-is)+1 + 2*(NGHOST);
    int nx2 = (je-js)+1 + 2*(NGHOST);
    int nx3 = (ke-ks)+1 + 2*(NGHOST);
    a1.NewAthenaArray(nx3,nx2,nx1);
    a2.NewAthenaArray(nx3,nx2,nx1);
    a3.NewAthenaArray(nx3,nx2,nx1);

    for (int k=ks; k<=ke+1; k++) {
      for (int j=js; j<=je+1; j++) {
        for (int i=is; i<=ie+1; i++) {
          a1(k,j,i) = A1(pcoord->x1v(i), pcoord->x2f(j), pcoord->x3f(k));
          a2(k,j,i) = A2(pcoord->x1f(i), pcoord->x2v(j), pcoord->x3f(k));
          a3(k,j,i) = A3(pcoord->x1f(i), pcoord->x2f(j), pcoord->x3v(k));
        }
      }
    }

    // Initialize interface fields
    AthenaArray<Real> area,len,len_p1;
    area.NewAthenaArray(nx1);
    len.NewAthenaArray(nx1);
    len_p1.NewAthenaArray(nx1);

    // for 1,2,3-D
    int jl=js; int ju=je+1;
    for (int k=ks; k<=ke; ++k) {
      // reset loop limits for polar boundary

      if ((pbval->block_bcs[BoundaryFace::inner_x2] == BoundaryFlag::polar) ||
        (pbval->block_bcs[BoundaryFace::inner_x2] == BoundaryFlag::polar_wedge))
        jl=js+1;
      if ((pbval->block_bcs[BoundaryFace::outer_x2] == BoundaryFlag::polar) ||
        (pbval->block_bcs[BoundaryFace::outer_x2] == BoundaryFlag::polar_wedge))
        ju=je;
      for (int j=jl; j<=ju; ++j) {
        pcoord->Face2Area(k,j,is,ie,area);
        pcoord->Edge3Length(k,j,is,ie+1,len);
        for (int i=is; i<=ie; ++i) {
          pfield->b.x2f(k,j,i) = -1.0*(len(i+1)*a3(k,j,i+1) - len(i)*a3(k,j,i))/area(i);
        }
      }
    }
    for (int k=ks; k<=ke+1; ++k) {
      for (int j=js; j<=je; ++j) {
        pcoord->Face3Area(k,j,is,ie,area);
        pcoord->Edge2Length(k,j,is,ie+1,len);
        for (int i=is; i<=ie; ++i) {
          pfield->b.x3f(k,j,i) = (len(i+1)*a2(k,j,i+1) - len(i)*a2(k,j,i))/area(i);
        }
      }
    }

    // for 2D and 3D
    if (block_size.nx2 > 1) {
      for (int k=ks; k<=ke; ++k) {
        for (int j=js; j<=je; ++j) {
          pcoord->Face1Area(k,j,is,ie+1,area);
          pcoord->Edge3Length(k,j  ,is,ie+1,len);
          pcoord->Edge3Length(k,j+1,is,ie+1,len_p1);
          for (int i=is; i<=ie+1; ++i) {
            pfield->b.x1f(k,j,i) = (len_p1(i)*a3(k,j+1,i) - len(i)*a3(k,j,i))/area(i);
          }
        }
      }
      for (int k=ks; k<=ke+1; ++k) {
        for (int j=js; j<=je; ++j) {
          pcoord->Face3Area(k,j,is,ie,area);
          pcoord->Edge1Length(k,j  ,is,ie,len);
          pcoord->Edge1Length(k,j+1,is,ie,len_p1);
          for (int i=is; i<=ie; ++i) {
            pfield->b.x3f(k,j,i) -= (len_p1(i)*a1(k,j+1,i) - len(i)*a1(k,j,i))/area(i);
          }
        }
      }
    }
    // for 3D only
    if (block_size.nx3 > 1) {
      for (int k=ks; k<=ke; ++k) {
        for (int j=js; j<=je; ++j) {
          pcoord->Face1Area(k,j,is,ie+1,area);
          pcoord->Edge2Length(k  ,j,is,ie+1,len);
          pcoord->Edge2Length(k+1,j,is,ie+1,len_p1);
          for (int i=is; i<=ie+1; ++i) {
            pfield->b.x1f(k,j,i) -= (len_p1(i)*a2(k+1,j,i) - len(i)*a2(k,j,i))/area(i);
          }
        }
      }
      for (int k=ks; k<=ke; ++k) {
        // reset loop limits for polar boundary
        int jl=js; int ju=je+1;
        if ((pbval->block_bcs[BoundaryFace::inner_x2] == BoundaryFlag::polar) ||
          (pbval->block_bcs[BoundaryFace::inner_x2] == BoundaryFlag::polar_wedge))
          jl=js+1;
        if ((pbval->block_bcs[BoundaryFace::outer_x2] == BoundaryFlag::polar) ||
          (pbval->block_bcs[BoundaryFace::outer_x2] == BoundaryFlag::polar_wedge))
          ju=je;
        for (int j=jl; j<=ju; ++j) {
          pcoord->Face2Area(k,j,is,ie,area);
          pcoord->Edge1Length(k  ,j,is,ie,len);
          pcoord->Edge1Length(k+1,j,is,ie,len_p1);
          for (int i=is; i<=ie; ++i) {
            pfield->b.x2f(k,j,i) += (len_p1(i)*a1(k+1,j,i) - len(i)*a1(k,j,i))/area(i);
          }
        }
      }
    }
    // Calculate cell-centered magnetic field
    AthenaArray<Real> bb;
    bb.NewAthenaArray(3, ke+1, je+1, ie+NGHOST+1);
    pfield->CalculateCellCenteredField(pfield->b, bb, pcoord, is-NGHOST, ie+NGHOST, js,
                                       je, ks, ke);

    for (int k=ks; k<=ke; k++) {
      for (int j=js; j<=je; j++) {
        for (int i=is; i<=ie; i++) {
          Real& bcc1 = bb(IB1,k,j,i);
          Real& bcc2 = bb(IB2,k,j,i);
          Real& bcc3 = bb(IB3,k,j,i);

          phydro->u(IEN,k,j,i) += 0.5*(SQR(bcc1)+SQR(bcc2)+SQR(bcc3));
         }
      }
    }
    a1.DeleteAthenaArray();
    a2.DeleteAthenaArray();
    a3.DeleteAthenaArray();
    area.DeleteAthenaArray();
    len.DeleteAthenaArray();
    len_p1.DeleteAthenaArray();
    bb.DeleteAthenaArray();
  } // end if MAGNETIC_FIELDS_ENABLED
}

// Source Terms
void heat_cool(MeshBlock *pmb, const Real time, const Real dt,
               const AthenaArray<Real> &prim, const AthenaArray<Real> &prim_scalar,
               const AthenaArray<Real> &bcc, AthenaArray<Real> &cons,
               AthenaArray<Real> &cons_scalar) {

  for (int k=pmb->ks; k<=pmb->ke; ++k) {
    for (int j=pmb->js; j<=pmb->je; ++j) {
      for (int i=pmb->is; i<=pmb->ie; ++i) {
        Real erg2MeV  = 6.24151e5;                    // Erg to MeV conversion factor
        Real r        = pmb->pcoord->x1v(i);          // Radial coordinate
        Real p        = prim(IPR,k,j,i);              // Pressure
        Real rho      = prim(IDN,k,j,i);              // Density
        Real kbol_MeV = 8.61733326*std::pow(10,-11);  // Boltzmann constant in MeV / K
        Real Ye_i     = prim_scalar(ye_index,k,j,i);  // Electron fraction before being updated in this function
        efrac         = &Ye_i;                        // Electron fraction pointer for EoS calls

        Real r_scalar[nscalar_size];
        Real s_scalar[nscalar_size];
        for (int ns=0; ns<nscalar_size; ns++) {
          r_scalar[ns] = prim_scalar(ns,k,j,i);
          s_scalar[ns] = cons_scalar(ns,k,j,i);
        }


        // Calculate source terms
//        Real temp   = pmb->peos->TFromRhoP(rho, p, efrac) * kbol_MeV;                // MeV
//        Real temp   = pmb->peos->TFromRhoP(rho, p, r_scalar) * kbol_MeV;                // MeV
        Real temp = prim_scalar(t_index,k,j,i) * kbol_MeV; // MeV
//        std::cout << "(heat_cool) temp = " << temp << " MeV" << std::endl;
//        std::cout << "(heat_cool) r    = " << r << " cm" << std::endl;
//        std::cout << " " << std::endl;
        if(std::isnan(Ye_i)) {
          std::cout << "(heat_cool) NANS (0) (Ye_i)" << std::endl;
          std::cout << "Ye_i  = " << Ye_i << std::endl;
          std::cout << "p     = " << p    << "erg/cm^3" <<std::endl;
          std::cout << "temp  = " << temp << "MeV" <<std::endl;
          std::cout << "rho   = " << rho  << "g/cm^3" <<std::endl;
          std::cout << " " << std::endl;
        }
        if(std::isnan(temp)) {
          std::cout << "(heat_cool) NANS (1) (temp)" << std::endl;
          std::cout << "Ye_i  = " << Ye_i << std::endl;
          std::cout << "p     = " << p    << "erg/cm^3" <<std::endl;
          std::cout << "temp  = " << temp << "MeV" <<std::endl;
          std::cout << "rho   = " << rho  << "g/cm^3" <<std::endl;
          std::cout << " " << std::endl;
        }
        Real X_n    = 1.0; //Xn(rho, temp);
        if (r>5.0e6) {
//        if (temp < 1.0) {
          X_n = X_nucleon(rho, temp);
        }
        Real x       = std::sqrt(1.0-(r_0*r_0)/(r*r));
        Real ExpSupp = std::exp(-1.0 * rho / rho_0);

//        Real vdYedr = 0.0; //std::min(1.0, X_n) * (YeSourceHEOS(temp,Ye_i,rho,r) - YeSinkHEOS(temp,Ye_i,rho,r));   // s^-1
//        Real vdYedr = std::min(1.0, X_n) * (YeSource_QW_Modified(rho,temp,Ye_i,x,r) - YeSink_QW_Modified(rho,temp,Ye_i,x,r));
        Real vdYedr = ExpSupp * std::min(1.0,X_n) * YeTejas(temp, Ye_i, x, rho);
//        Real qdot   = std::min(1.0, X_n) * (qdotScheck_H(Ye_i,r) - qdotScheck_C(temp/kbol_MeV,Ye_i,rho,r)); // erg/s/g units
     //   Real qdot = std::min(1.0,X_n) * (Heating_QW_Modified(x, Ye_i) - Cooling_QW_Modified(rho, temp, Ye_i));
      //  Real qdot = qdotQW(temp, x, Ye_i, time) / erg2MeV;
        Real qdot   = ExpSupp * std::min(1.0,X_n) * (Heating_QW_Modified(x, Ye_i) - Cooling_QW_Modified(rho, temp, Ye_i)); // erg/s/g
//        std::cout << "qdot = " << qdot << " erg/s/g" << std::endl;
//        if(std::isnan(YeSourceHEOS(temp,Ye_i,rho,r)) || std::isnan(YeSinkHEOS(temp,Ye_i,rho,r))) {
//          if(std::isnan(YeSourceHEOS(temp,Ye_i,rho,r))) {
//            std::cout << "Source gives NaN" << std::endl;
//          }
//          if(std::isnan(YeSinkHEOS(temp,Ye_i,rho,r))) {
//            std::cout << "Sink gives NaN" << std::endl;
//          }
//          std::cout << "r                    = " << r << " cm" << std::endl;
//          std::cout << "P(in troubled zone)  = " << p << " erg/cm^3" << std::endl;
//          std::cout << "rho(in troubled zone)= " << rho << " g/cm^3" << std::endl;
//	  std::cout << "Ye(in troubled zone) = " << Ye_i << std::endl;
//	  std::cout << "T(in troubled zone)  = " << temp << " MeV" << std::endl;
//          std::cout << " "  << std::endl;
//        }

        // Find electron fraction and energy increments
        Real dYe = dt*vdYedr;
        Real de  = dt*prim(IDN,k,j,i) * qdot; // erg/cm^-3

        // Update conserved composition and energy fields
        cons_scalar(ye_index,k,j,i) += dYe*prim(IDN,k,j,i); // g cm^-3
        if (cons(IEN,k,j,i)>1.0e50) {
          std::cout << "(helm_eos) before e update:" << std::endl;
          std::cout << "e = " << cons(IEN,k,j,i) << std::endl;
          std::cout << "r = " << r << " cm" << std::endl;
        }
        cons(IEN,k,j,i) += de;                              // erg/cm^3
        if(cons(IEN,k,j,i)>1.0e50) {
          std::cout << "(heat_cool) dt   = " << dt << " s" << std::endl;
          std::cout << "            r    = " << r    << " cm" << std::endl;
          std::cout << "            E    = " << cons(IEN,k,j,i) << std::endl;
          std::cout << "            rho  = " << rho  << " g/cm^3" << std::endl;
          std::cout << "            P    = " << p    << " erg/cm^3" << std::endl;
          std::cout << "         T (MeV) = " << temp    << " MeV" << std::endl;
          std::cout << "           T (K) = " << temp / kbol_MeV << " K" << std::endl;
          std::cout << "            Ye   = " << Ye_i << std::endl;
          std::cout << "           qdot  = " << qdot << " erg/s/g" << std::endl;

        }
        if(std::isnan(cons_scalar(ye_index,k,j,i))) {
          std::cout << "(heat_cool) NANS (2) (cons_scalar)" << std::endl;
          std::cout << "Ye_i  = " << Ye_i << std::endl;
          std::cout << "p     = " << p    << "erg/cm^3" <<std::endl;
          std::cout << "temp  = " << temp << "MeV" <<std::endl;
          std::cout << "rho   = " << rho  << "g/cm^3" <<std::endl;
          std::cout << " " << std::endl;
        }
      }
    }
  }
  return;
}

// Inflow Boundary Condition
void InflowInnerX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                   FaceField &b, Real time, Real dt, int is, int ie, int js,
                   int je, int ks, int ke, int ngh) {

  Real rho_new;
  AthenaArray<int>& my_data1 = pmb->pmy_mesh->iuser_mesh_data[0];
  AthenaArray<Real>& my_data2 = pmb->pmy_mesh->ruser_mesh_data[6];
  AthenaArray<Real>& my_data3 = pmb->pmy_mesh->ruser_mesh_data[7];

  Real &rho_old{my_data2(0)};
  Real &T_equilibrium{my_data3(0)};
  // Ncycle is updated twice per time cycle because there are two steps in 1 time cycle
  int &ncycle_x2{my_data1(0)};
  if (time == 0.0) {
    ncycle_x2 = 0;
  } else {
    ncycle_x2 += 1;
  }

  // Divide ncycle_x2 by 2 to get the actual cycle number
  Real ncycle = ncycle_x2 / 2.0;
  int Roundncycle = round(ncycle);

  // Global tau is calcated in UserWorkInLoop
  Real tau = global_tau;
  // Final zone velocity, used to determine if an explosion has occured
  Real Vr_FZ = Vr_FinalActiveZone;

  // perturb base density every n'th cycle
  if (Roundncycle == ncycle) {
    if (Roundncycle % nthcycle == 0) {
      if (time != 0.0) {
        if ((tau < tau_v * (1.0 + tau_epsilon)) && (tau > tau_v * (1.0 - tau_epsilon))){
          rho_new = rho_old;
          std::cout << "converged" << std::endl;
          std::cout << "ncycle  = " << ncycle << std::endl;
          std::cout << "rho_new = " << rho_new << " g/cm^3" << std::endl;
          std::cout << "active  = " << prim(IDN,ks,js,is) << " g/cm^3" << std::endl;
          std::cout << "tau     = " << tau << std::endl;
          std::cout << "time    = " << time << " s" << std::endl;
        } else if (tau < tau_v * (1.0 - tau_epsilon)) {
          // if in an explosion regime, dont update rho
          if(Vr_FZ <= 0.0) {
            rho_new = rho_old * (1.0 + rho_epsilon);
          } else {
            std::cout << "Vr(Last Active Zone) = " << Vr_FZ << " cm/s" << std::endl;
            rho_new = rho_old;
          }
          std::cout << "too small" << std::endl;
          std::cout << "ncycle  = " << ncycle << std::endl;
          std::cout << "rho_new = " << rho_new << " g/cm^3" << std::endl;
          std::cout << "active  = " << prim(IDN,ks,js,is) << " g/cm^3" << std::endl;
          std::cout << "tau     = " << tau << std::endl;
          std::cout << "time    = " << time << " s" << std::endl;
        } else if (tau > tau_v * (1.0 + tau_epsilon)) {
          // if in an explosion regime, dont update rho
          if(Vr_FZ <= 0.0) {
            rho_new = rho_old * (1.0 - rho_epsilon);
          } else {
            std::cout << "Vr(Last Active Zone) = " << Vr_FZ << " cm/s" << std::endl;
            rho_new = rho_old;
          }
          std::cout << "too big" << std::endl;
          std::cout << "ncycle  = " << ncycle << std::endl;
          std::cout << "rho_new = " << rho_new << " g/cm^3" << std::endl;
          std::cout << "active  = " << prim(IDN,ks,js,is) << " g/cm^3" << std::endl;
          std::cout << "tau     = " << tau << std::endl;
          std::cout << "time    = " << time << " s" << std::endl;
        } else {
          std::cout << "(accretion.cpp) Somehow I've subverted the tau conditional statements. Something isn't right." << std::endl;
        }
      } else {
        std::cout << "t = 0, using default rho0" << std::endl;
        rho_new = rho_0;
        rho_old = rho_new;
      }
    } else {
      if (time == 0.0 || ncycle < 1.0) {
        // Use user-specified base density at t=0
        std::cout << "time = 0s or ncycle < 1, using default rho0" << std::endl;
        rho_new = rho_0;
        rho_old = rho_new;
      } else {
        // Use ghost zone value from previous cycle (this assumes that an HSE profile isn't being set in the ghost zones).
        rho_new = rho_old;
      }
    }
  } else {
    if (time == 0.0 || ncycle < 1.0) {
      // Use user-specified base density at t=0
      std::cout << "time = 0s or ncycle < 1, using default rho0" << std::endl;
      rho_new = rho_0;
      rho_old = rho_new;
    } else {
        rho_new = rho_old;
    }
  }

  // Just sending in input values here because I don't feel like messing with double NR right now
  Real* Yeq_ptr  = &ye_0;
//  Real Arr[1];
//  Single_NR(Arr,r_0);
//  Real Teq = Arr[0];
//  Real T_g       = T_0;

  for (int k=ks; k<=ke; ++k) {
    for (int j=js; j<=je; ++j) {
      Real theta = pco->x2v(j);
      for (int i=1; i<=ngh; ++i) {
          prim(IDN,k,j,is-i)                  = rho_new;
          rho_old                             = prim(IDN,k,j,is-i);
          prim(IVX,k,j,is-i)                  = prim(IVX,k,j,is);
          prim(IVY,k,j,is-i)                  = 0.0;
          prim(IVZ,k,j,is-i)                  = 0.0;
          Real ye_a                           = pmb->pscalars->r(ye_index,k,j,is);
          Real rho_a                          = prim(IDN,k,j,is);
          Real r_a                            = pco->x1v(is);
          pmb->pscalars->r(ye_index,k,j,is-i) = ye_a;
          Real* ye_g                          = &pmb->pscalars->r(ye_index,k,j,is-i);

          // Single NR step to find equilibrium temperature
          Real Arr[1];
          Single_NR(Arr, r_a, rho_a, ye_a);
          Real Teq      = Arr[0];
          T_equilibrium = Teq;
          pmb->pscalars->r(t_index,k,j,is-i) = Teq;
//          pmb->pscalars->r(t_index,k,j,is-i) = pmb->pscalars->r(t_index,k,j,is);

          Real r_scalar[nscalar_size];
          Real s_scalar[nscalar_size];
          for (int ns=0; ns<nscalar_size; ns++) {
            r_scalar[ns] = pmb->pscalars->r(ns,k,j,is-i);
            s_scalar[ns] = pmb->pscalars->s(ns,k,j,is-i);
          }

          if (NON_BAROTROPIC_EOS) {
            prim(IPR,k,j,is-i) = pmb->peos->PresFromRhoT(rho_new, Teq, r_scalar); //This one works for tau
//            prim(IPR,k,j,is-i) = pmb->peos->PresFromRhoT(rho_new, pmb->pscalars->r(t_index,k,j,is), r_scalar);
          }
      }
    }
  }

  // copy face-centered magnetic fields into ghost zones
  if (MAGNETIC_FIELDS_ENABLED) {
    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x1f(k,j,(is-i)) = b.x1f(k,j,is);
        }
      }
    }

    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je+1; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x2f(k,j,(is-i)) = b.x2f(k,j,is);
        }
      }
    }

    for (int k=ks; k<=ke+1; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x3f(k,j,(is-i)) = b.x3f(k,j,is);
        }
      }
    }
  }
}

// Inflow Boundary Condition
void InflowMdotInnerX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                   FaceField &b, Real time, Real dt, int is, int ie, int js,
                   int je, int ks, int ke, int ngh) {
  Real r0 = pco->x1v(is);
  Real Arr[2];
  Double_NR(Arr,r0,rho_0);

  T_eq           = Arr[0];
  Ye_eq          = Arr[1];
  Real* Yeq_ptr  = &Ye_eq;
  Real p_0       = pmb->peos->PresFromRhoT(rho_0, T_eq, Yeq_ptr);

  for (int k=ks; k<=ke; ++k) {
    // Real phi = pco->x3v(k);
    for (int j=js; j<=je; ++j) {
      Real theta = pco->x2v(j);
      for (int i=1; i<=ngh; ++i) {
        prim(IDN,k,j,is-i) = rho_0;
        Real v = prim(IVX,k,j,is) * SQR(pco->x1v(is) / pco->x1v(is-i));
        prim(IVX,k,j,is-i) = std::max(v, 0.0);
        prim(IVY,k,j,is-i) = 0.0;
        prim(IVZ,k,j,is-i) = 0.0;
        if (NON_BAROTROPIC_EOS)
          prim(IPR,k,j,is-i) = p_0;
      }
    }
  }

  // copy face-centered magnetic fields into ghost zones
  if (MAGNETIC_FIELDS_ENABLED) {
    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x1f(k,j,(is-i)) = b.x1f(k,j,is);
        }
      }
    }

    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je+1; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x2f(k,j,(is-i)) = b.x2f(k,j,is);
        }
      }
    }

    for (int k=ks; k<=ke+1; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x3f(k,j,(is-i)) = b.x3f(k,j,is);
        }
      }
    }
  }
}

void HSEInnerX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                FaceField &b, Real time, Real dt, int is, int ie, int js,
                int je, int ks, int ke, int ngh) {

  Real r0 = pco->x1v(is);
  Real Arr[2];
  Double_NR(Arr,r0,rho_0);

  T_eq           = Arr[0];
  Ye_eq          = Arr[1];
  Real* Yeq_ptr  = &Ye_eq;
  Real p_0       = pmb->peos->PresFromRhoT(rho_0, T_eq, Yeq_ptr);
  dpdd_0         = pmb->peos->AsqFromRhoP(rho_0, p_0, Yeq_ptr);

  for (int k=ks; k<=ke; ++k) {
    // Real phi = pco->x3v(k);
    for (int j=js; j<=je; ++j) {
      Real theta = pco->x2v(j);
      for (int i=1; i<=ngh; ++i) {
        Real r = pco->x1v(is-i);
        prim(IDN,k,j,is-i) = rho_0 * std::exp((r0 - r) * mu / (dpdd_0 * r * r0));
        Real v = prim(IVX,k,j,is) * prim(IDN,k,j,is) / prim(IDN,k,j,is-i) * SQR(r0 / r);
        prim(IVX,k,j,is-i) = std::max(v, 0.0);
        prim(IVY,k,j,is-i) = 0.0;
        prim(IVZ,k,j,is-i) = 0.0;
        if (NON_BAROTROPIC_EOS) {
          prim(IPR,k,j,is-i) = pmb->peos->PresFromRhoT(prim(IDN,k,j,is-i), T_eq, Yeq_ptr);
        }
      }
    }
  }

  // copy face-centered magnetic fields into ghost zones
  if (MAGNETIC_FIELDS_ENABLED) {
    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x1f(k,j,(is-i)) = b.x1f(k,j,is);
        }
      }
    }

    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je+1; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x2f(k,j,(is-i)) = b.x2f(k,j,is);
        }
      }
    }

    for (int k=ks; k<=ke+1; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x3f(k,j,(is-i)) = b.x3f(k,j,is);
        }
      }
    }
  }
}

void HSE2InnerX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                 FaceField &b, Real time, Real dt, int is, int ie, int js,
                int je, int ks, int ke, int ngh) {
  AthenaArray<Real> out1;
  out1.NewAthenaArray(7);
  Real r0 = pco->x1v(is);
  Real Arr[2];
  Double_NR(Arr,r0,rho_0);

  T_eq           = Arr[0];
  Ye_eq          = Arr[1];
  Real* Yeq_ptr  = &Ye_eq;
  for (int k=ks; k<=ke; ++k) {
    // Real phi = pco->x3v(k);
    for (int j=js; j<=je; ++j) {
      Real theta = pco->x2v(j);
      for (int i=1; i<=ngh; ++i) {
        Real r = pco->x1v(is-i);
        prim(IDN,k,j,is-i) = rho_0 * std::exp((r0 - r) * mu / (dpdd_0 * r * r0));
        prim(IVX,k,j,is-i) = std::max(prim(IVX,k,j,is), 0.0);
        prim(IVY,k,j,is-i) = 0.0;
        prim(IVZ,k,j,is-i) = 0.0;
        if (NON_BAROTROPIC_EOS) {
          prim(IPR,k,j,is-i) = pmb->peos->PresFromRhoT(prim(IDN,k,j,is-i), T_eq, Yeq_ptr);
        }
      }
    }
  }

  // copy face-centered magnetic fields into ghost zones
  if (MAGNETIC_FIELDS_ENABLED) {
    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x1f(k,j,(is-i)) = b.x1f(k,j,is);
        }
      }
    }

    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je+1; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x2f(k,j,(is-i)) = b.x2f(k,j,is);
        }
      }
    }

    for (int k=ks; k<=ke+1; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x3f(k,j,(is-i)) = b.x3f(k,j,is);
        }
      }
    }
  }
}

// Outflow Boundary Condition
void OutflowOuterX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                   FaceField &b, Real time, Real dt, int is, int ie, int js,
                   int je, int ks, int ke, int ngh) {
  Real re = pco->x1v(ie);
  for (int k=ks; k<=ke; ++k) {
    for (int j=js; j<=je; ++j) {
      for (int i=1; i<=ngh; ++i) {
        Real rgh = pco->x1v(ie+i);
        Real ratio = re / rgh;
        prim(IDN,k,j,ie+i) = prim(IDN,k,j,ie) * SQR(ratio);
        prim(IVX,k,j,ie+i) = std::max(prim(IVX,k,j,ie), 0.0);
        prim(IVY,k,j,ie+i) = prim(IVY,k,j,ie) * ratio;
        prim(IVZ,k,j,ie+i) = prim(IVZ,k,j,ie) * ratio;
        if (NON_BAROTROPIC_EOS)
          prim(IPR,k,j,ie+i) = prim(IPR,k,j,ie); // Constant Pressure
      }
    }
  }

  // copy face-centered magnetic fields into ghost zones
  if (MAGNETIC_FIELDS_ENABLED) {
    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x1f(k,j,(ie+i+1)) = b.x1f(k,j,(ie+1));
        }
      }
    }
    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je+1; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x2f(k,j,(ie+i)) = b.x2f(k,j,ie);
        }
      }
    }
    for (int k=ks; k<=ke+1; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x3f(k,j,(ie+i)) = b.x3f(k,j,ie);
        }
      }
    }
  }
}

// Inflow Boundary Condition at outer boundary
void InflowOuterX1(MeshBlock *pmb, Coordinates *pco, AthenaArray<Real> &prim,
                   FaceField &b, Real time, Real dt, int is, int ie, int js,
                   int je, int ks, int ke, int ngh) {
  AthenaArray<Real>& DATA = pmb->pmy_mesh->ruser_mesh_data[8];
  Real &P_Ghost{DATA(0)};

  for (int k=ks; k<=ke; ++k) {
    for (int j=js; j<=je; ++j) {
      Real theta = pco->x2v(j);
      for (int i=1; i<=ngh; ++i) {
	Real rmax   = pco->x1v(ie);
        Real vmax   = prim(IVX,k,j,ie);
        Real Msun   = 1.989e33; // Msun in grams
        Real rhomax = (Mdot * Msun) / (4.0 * PI * std::pow(rmax,2.0) * std::fabs(vmax));
        if (prim(IVX,k,j,ie) < 0.0) {
          prim(IDN,k,j,ie+i) = rhomax;
          prim(IVX,k,j,ie+i) = vmax;
          prim(IVY,k,j,ie+i) = 0.0;
          prim(IVZ,k,j,ie+i) = 0.0;
        } else {
          prim(IDN,k,j,ie+i) = prim(IDN,k,j,ie); //prim(IDN,k,j,ie);
          prim(IVX,k,j,ie+i) = vmax;  //prim(IVX,k,j,ie);
          prim(IVY,k,j,ie+i) = 0.0;
          prim(IVZ,k,j,ie+i) = 0.0;

        }
        pmb->pscalars->r(ye_index,k,j,ie+i) = ye_f;
        // initialize temperature to floating
        pmb->pscalars->r(t_index,k,j,ie+i)  = pmb->pscalars->r(t_index,k,j,ie);
//	Real* ye_ptr = pmb->pscalars->r(ye_index,k,j,ie+i);
        Real r_scalar[nscalar_size];
        Real s_scalar[nscalar_size];
        for (int ns=0; ns<nscalar_size; ns++) {
          r_scalar[ns] = pmb->pscalars->r(ns,k,j,ie+i);
          s_scalar[ns] = pmb->pscalars->s(ns,k,j,ie+i);
        }

        if (NON_BAROTROPIC_EOS) {
     //     std::cout << "(PGEN) InflowOuterX1:" << std::endl;
     //     std::cout << "p_f (input for GZ) = " << p_f << " erg/cm^3" << std::endl;
     //     std::cout << "pModify            = " << pModify << std::endl;
     //     std::cout << "p_f (active zone)  = " << prim(IPR,k,j,ie) << " erg/cm^3" << std::endl;
          Real P_IC = p_f;
//          pmb->pscalars->r(t_index,k,j,ie+i) = pmb->peos->TFromRhoP(prim(IDN,k,j,ie+i),P_IC,r_scalar);
          // Repopulate the T scalar array with newly acquired T_ghost
 //         for (int ns=0; ns<nscalar_size; ns++) {
 //           r_scalar[ns] = pmb->pscalars->r(ns,k,j,ie+i);
 //           s_scalar[ns] = pmb->pscalars->s(ns,k,j,ie+i);
 //         }
          Real gamma         = pmb->peos->GammaFromRhoT(prim(IDN,k,j,ie+i),pmb->pscalars->r(t_index,k,j,ie+i),r_scalar);
          prim(IPR,k,j,ie+i) = rhomax * std::pow(vmax,2.0) / (gamma * std::pow(Mach,2.0)); // Constant Pressure
          P_GZ               = prim(IPR,ke,je,ie+1);
          P_Ghost            = P_GZ;
  //        pmb->pscalars->r(t_index,k,j,ie+i)=pmb->peos->TFromRhoP(prim(IDN,k,j,ie+i),prim(IPR,k,j,ie+i),r_scalar);
        }
      }
    }
  }

  // copy face-centered magnetic fields into ghost zones
  if (MAGNETIC_FIELDS_ENABLED) {
    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x1f(k,j,(ie+i+1)) = b.x1f(k,j,(ie+1));
        }
      }
    }
    for (int k=ks; k<=ke; ++k) {
      for (int j=js; j<=je+1; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x2f(k,j,(ie+i)) = b.x2f(k,j,ie);
        }
      }
    }
    for (int k=ks; k<=ke+1; ++k) {
      for (int j=js; j<=je; ++j) {
#pragma omp simd
        for (int i=1; i<=ngh; ++i) {
          b.x3f(k,j,(ie+i)) = b.x3f(k,j,ie);
        }
      }
    }
  }
}

void MeshBlock::UserWorkInLoop() {
  AthenaArray<Real>& my_data = pmy_mesh->ruser_mesh_data[5];
  Real &local_sum{my_data(0)};
  Real t = pmy_mesh->time;
  Real sigma_nue_n = sigma_0 * ((1.0 + 3.0 * std::pow(g_a,2)) / (4.0)) * std::pow(((eps_nue + delta_np) / (mcsq)),2);
  Real testrho = phydro->w(IDN,ks,js,is);
  if (lid == 0) {
    local_sum = 0.0;
  }
  for (int k=ks; k<=ke; ++k) {
    for (int j=js; j<=je; ++j) {
      for (int i=is; i<=ie-1; ++i) {
        Real rho_ip1 = phydro->w(IDN,k,j,i+1);
        Real rho_i   = phydro->w(IDN,k,j,i);
        Real r_ip1   = pcoord->x1v(i+1);
        Real r_i     = pcoord->x1v(i);
        Real ye_ip1  = pscalars->r(ye_index,k,j,i+1);
        Real ye_i    = pscalars->r(ye_index,k,j,i);
        Real Chi_ip1 = (1.0 - ye_ip1);
        Real Chi_i   = (1.0 - ye_i);
        Real deltaR  = r_ip1 - r_i;
        local_sum    += 0.5 * deltaR * sigma_nue_n * Na * ((Chi_ip1 * rho_ip1) + (Chi_i * rho_i));
      }
    }
  }
  if (lid == pmy_mesh->nblocal-1) {
    Real global_integral;
    MPI_Allreduce(&local_sum, &global_integral, 1,
                  MPI_ATHENA_REAL, MPI_SUM, MPI_COMM_WORLD);
    global_tau = global_integral;
    Vr_FinalActiveZone = phydro->w(IVX,ke,je,ie);
  }
}

void MeshBlock::UserWorkBeforeOutput(ParameterInput *pin) {
  for(int k=ks; k<=ke; k++) {
    for(int j=js; j<=je; j++) {
      for(int i=is; i<=ie; i++) {
        efrac         = &pscalars->r(ye_index,k,j,i);
     //   Real temp     = peos->TFromRhoP(phydro->w(IDN,k,j,i),phydro->w(IPR,k,j,i),efrac); // units of K
        Real temp     = pscalars->r(t_index,k,j,i);
        Real r        = pcoord->x1v(i);
        Real x        = std::pow((1.0-(r_0*r_0)/(r*r)),0.5);
        Real kbol_MeV = 8.61733326*std::pow(10,-11);                                      // Boltzmann constant in MeV / K
        Real ye       = pscalars->r(ye_index,k,j,i);
        Real rho      = phydro->w(IDN,k,j,i);
        Real erg2MeV  = 6.24151e5;

        // Read in T_equilibrium
        AthenaArray<Real>& my_data = pmy_mesh->ruser_mesh_data[7];
        AthenaArray<Real>& DATA    = pmy_mesh->ruser_mesh_data[8];
        Real &Tequil{my_data(0)};
        Real &P_GhostZ{DATA(0)};
//        std::cout << "P_GhostZ (Output step) = " << P_GhostZ << " erg/cm^3" << std::endl;

        Real temp_MeV = temp * kbol_MeV;
        Real t = pmy_mesh->time;
        Real X_n    = 1.0; //Xn(rho, temp);
        if (r>5.0e6) {
//        if (temp < 1.0) {
          X_n = X_nucleon(rho, temp);
        }
        Real ExpSupp = std::exp(-1.0 * rho / rho_0);

        // Define user output variables:
        // Temperature
        user_out_var(0,k,j,i) = temp;
        // Qdot = H - C
//        user_out_var(1,k,j,i) = qdotScheck_H(pscalars->r(ye_index,k,j,i),r)
//                                - qdotScheck_C(temp,pscalars->r(ye_index,k,j,i),phydro->u(IDN,k,j,i),r);
//        user_out_var(1,k,j,i) = qdotQW(temp_MeV, x, ye, t) / erg2MeV;
        user_out_var(1,k,j,i) = ExpSupp * std::min(1.0, X_n) * (Heating_QW_Modified(x, ye) - Cooling_QW_Modified(rho, temp_MeV, ye));
        // Sound Speed
//        std::cout << "(Pgen, Userworkbeforeoutput) Before Asq" << std::endl;
//        std::cout << "temp     = " << temp << " K" << std::endl;
//        std::cout << "pressure = " << phydro->w(IPR,k,j,i) << " erg/cm^3" << std::endl;
//        std::cout << "ye       = " << pscalars->r(ye_index,k,j,i) << std::endl;
//        std::cout << "rho (w)  = " << phydro->w(IDN,k,j,i) << " g/cm^3" << std::endl;
//        std::cout << "rho (u)  = " << phydro->u(IDN,k,j,i) << " g/cm^3" << std::endl;

        user_out_var(2,k,j,i) = std::sqrt(peos->AsqFromRhoP(phydro->w(IDN,k,j,i),
                                                            phydro->w(IPR,k,j,i),efrac));
        // Tau value
        user_out_var(6,k,j,i) = global_tau;
        // Ghost zone values
        user_out_var(7,k,j,i)  = phydro->w(IDN,k,j,0);
        user_out_var(8,k,j,i)  = P_GhostZ; // outer ghost zone
        user_out_var(9,k,j,i)  = phydro->w(IVX,k,j,0);
        user_out_var(10,k,j,i) = pscalars->r(ye_index,k,j,0);
        user_out_var(11,k,j,i) = Tequil;
      }
    }
  }
}
