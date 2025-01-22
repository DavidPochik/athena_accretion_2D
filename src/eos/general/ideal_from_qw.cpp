#define MYDEBUG1
//========================================================================================
// Athena++ astrophysical MHD code
// Copyright(C) 2014 James M. Stone <jmstone@princeton.edu> and other code contributors
// Licensed under the 3-clause BSD License, see LICENSE file for details
//======================================================================================

// C headers

// C++ headers
#include <algorithm>
#include <cmath>   // sqrt()
#include <fstream>
#include <iostream> // ifstream
#include <limits>   // std::numeric_limits<float>::epsilon()
#include <sstream>
#include <stdexcept> // std::invalid_argument
#include <string>

// Athena++ headers
#include "../../athena.hpp"
#include "../../athena_arrays.hpp"
#include "../../coordinates/coordinates.hpp"
#include "../../field/field.hpp"
#include "../../parameter_input.hpp"
#include "../eos.hpp"

// Same effect as adding static to everything inside
namespace {
  // const Real float_eps = std::numeric_limits<Real>::epsilon();
  // const Real float_1pe = 1.0 + float_eps;
  const Real float_max = std::numeric_limits<Real>::max();
  Real prec = 1e-8;
  Real T_floor, T_ceil, LastTemp;
  Real fixed_ye = -1.0;
  int i_ye = -1;
  bool use_T_floor;
  int nmax;
  AthenaArray<Real> EosData;

  const Real third = 1.0 / 3.0;
  const Real c = 2.99792458e10;
  const Real k = 1.380649e-16;
  const Real mn = 1.6726e-24;
  const Real hbar = 6.62607015e-27/(2.0*PI);
  const Real c3 = std::pow(k/(hbar*c),3);
  const Real con3 = (11.0*PI*PI/180.0)*c3*k;
  const Real Tmin=1e3;
  const Real Tmax=1e15;
  const Real kmn=k/mn;
  const Real thel= 30.0/11.0;
  const Real fiel= 15.0/11.0;
  const Real eta_den_const = std::pow(6.0,2.0*third);
} // namespace

// EOS data indicies
namespace EOS {
  enum EosIndex {iE=0, idEdT=1, iP=2, idPdT=3, iAsq=4, iT=5, N=6};
}


Real PorE(Real rho, Real T, Real Ye, int index) {
  Real p0 = rho*kmn*T;
  if (index == EOS::iP) {
    return p0;
  } else if (index == EOS::iE) {
    return 1.5*p0;
  }
  std::cout<<"Incorrect index in PorE \n";
  return 0;
}




void IGData(Real rho, Real T, Real Ye, AthenaArray<Real> &OutData) {
  Real p0 = rho*kmn*T;
  Real P = p0;
  Real e = 1.5*p0;

  Real der_P= rho*kmn;
  Real der_e= 1.5*rho*kmn;

  Real ctsq=kmn*T;
  Real D=(T/rho)*der_P;
  Real cv= der_e / rho;
  Real asq = ctsq+D*D/(cv*T);

  OutData(0) = e;
  OutData(1) = der_e;
  OutData(2) = P;
  OutData(3) = der_P;
  OutData(4) = asq;
  OutData(5) = T;

#ifdef MYDEBUG1
  bool flag = false;
  for (int i=0; i<6; ++i) {
    if (!std::isfinite(OutData(i)))
      flag = true;
  }
  if (flag) {
    printf("ERR: Non-finite output detected in EOS output.\n");
    printf("e_int, de/dT, P_gas, dP/dT,   a^2,  Temp,  dens\n");
    printf("EOS data: ");
    for (int i=0; i<6; ++i)
      printf("%.4e, ", OutData(i));
    printf("%.4e\n", rho);
    std::stringstream msg;
    msg << "### FATAL ERROR in IGData" << std::endl
        << "Non-finite value in EOS data." << std::endl;
    ATHENA_ERROR(msg);
  }
#endif // MYDEBUG1
}




// index = 0 for internal energy; index = 2 for pressure; var = int energy or pressure
void TempInvert(Real rho, Real Ye, Real var, const int index,
                AthenaArray<Real> &OutData) {
  if ((std::isnan(var)) || (std::isnan(rho))) {
      const char *varnames[] = {"e_int", "de_int/dT", "P_gas", "dP/dT", "a^2", "T"};
      printf("ERR (%s): %.4e, rho: %.4e \n", varnames[index],var,rho);

      std::stringstream msg;
      msg <<"Nan in root find (var) \n";
      ATHENA_ERROR(msg);
    }
  if ((var<=0.0) || (rho<=0.0)) {
      const char *varnames[] = {"e_int", "de_int/dT", "P_gas", "dP/dT", "a^2", "T"};
      printf("ERR (%s): %.4e, rho: %.4e \n", varnames[index],var,rho);

      std::stringstream msg;
      msg <<"Negative var\n";
      ATHENA_ERROR(msg);
  }

  if (index == EOS::iP) {
    Real tt1= var/kmn;
    IGData(rho,tt1,Ye, OutData);
    return;
  }

  if (index == EOS::iE) {
    Real tt1= var/(1.5*kmn);
    IGData(rho,tt1,Ye, OutData);
    return;
  }
}

//----------------------------------------------------------------------------------------
//! \fn Real EquationOfState::PresFromRhoEg(Real rho, Real egas)
//  \brief Return gas pressure
Real EquationOfState::PresFromRhoEg(Real rho, Real egas, Real* s) {
  Real ye = fixed_ye;

  if (NSCALARS > 0 && i_ye >= 0) {

      ye = s[i_ye]/rho;
   
   }
  //std::cout<<"In EOS Presfromrhoeg   "<<ye<<"\n";
  TempInvert(rho, ye, egas, EOS::iE, EosData);
  return EosData(EOS::iP);
}

//----------------------------------------------------------------------------------------
//! \fn Real EquationOfState::EgasFromRhoP(Real rho, Real pres)
//  \brief Return internal energy density
Real EquationOfState::EgasFromRhoP(Real rho, Real pres, Real* r) {
  Real ye = fixed_ye;
  if (NSCALARS > 0 && i_ye >= 0) {

      ye = r[i_ye];
  }   
  //std::cout<<"In EOS egasfromrhoP   "<<ye<<"\n";
  TempInvert(rho, ye, pres, EOS::iP, EosData);
  return EosData(EOS::iE);
}

//----------------------------------------------------------------------------------------
//! \fn Real EquationOfState::AsqFromRhoP(Real rho, Real pres)
//  \brief Return adiabatic sound speed squared
Real EquationOfState::AsqFromRhoP(Real rho, Real pres, const Real* r) {
  Real ye = fixed_ye;
  if (NSCALARS > 0 && i_ye >= 0) {

      ye = r[i_ye];
  
  }
  //std::cout<<"In EOS Asq   "<<ye<<"\n";
  TempInvert(rho, ye, pres, EOS::iP, EosData);
  return EosData(EOS::iAsq);
}

void EquationOfState::SevenFromRhoT(Real rho, Real T, AthenaArray<Real> &out, Real* r) {
  Real ye = fixed_ye;
  if (NSCALARS > 0 && i_ye >= 0) {
    ye = r[i_ye];
  }
  IGData(rho, T, ye, out);
}

Real EquationOfState::TFromRhoP(Real rho, Real pres, Real* r) {
  Real ye = fixed_ye;
  if (NSCALARS > 0 && i_ye >= 0) {
    ye = r[i_ye];
  }
  TempInvert(rho, ye, pres, EOS::iP, EosData);
  return EosData(EOS::iT);
}

Real EquationOfState::TFromRhoEgas(Real rho, Real egas, Real* s) {
  Real ye = fixed_ye;
  if (NSCALARS > 0 && i_ye >= 0) {
    ye = s[i_ye] / rho;
  }
  TempInvert(rho,ye, egas, EOS::iE, EosData);
  return EosData(EOS::iT);
}

Real EquationOfState::PresFromRhoT(Real rho, Real T, Real* r) {
  Real ye = fixed_ye;
  if (NSCALARS > 0 && i_ye >= 0) {
    ye = r[i_ye];
  }
  IGData(rho, T, ye, EosData);
  return EosData(EOS::iP);
}

Real EquationOfState::GetEgasFloor(Real rho, Real* s) {
  Real ye = fixed_ye;
  if (NSCALARS > 0 && i_ye >= 0) {
    ye = s[i_ye] / rho;
  }
  IGData(rho, T_floor, ye, EosData);
  return EosData(EOS::iE);
  
}

Real EquationOfState::GetPresFloor(Real rho, Real* r) {
  Real ye = fixed_ye;
  if (NSCALARS > 0 && i_ye >= 0) {
    ye = r[i_ye];
  }
  IGData(rho, T_floor, ye, EosData);
  return EosData(EOS::iP);
  
}

//----------------------------------------------------------------------------------------
//! \fn void EquationOfState::InitEosConstants(ParameterInput* pin)
//! \brief Initialize constants for EOS
void EquationOfState::InitEosConstants(ParameterInput* pin) {
  EosData.NewAthenaArray(EOS::N);
  prec = pin->GetOrAddReal("hydro", "InversionPrecision", prec);
  if (pin->DoesParameterExist("hydro", "eos_ye")) {
    fixed_ye = pin->GetReal("hydro", "eos_ye");
  }
  if (pin->DoesParameterExist("hydro", "eos_ye_index")) {
    i_ye = pin->GetInteger("hydro", "eos_ye_index");
    if (i_ye < 0 || i_ye >= NSCALARS) {
      std::stringstream msg;
      msg << "### FATAL ERROR in EquationOfState::InitEosConstants" << std::endl
          << "hydro/eos_ye_index must be between 0 and NSCALARS (" << NSCALARS << ")."
          << std::endl;
      ATHENA_ERROR(msg);
    }
  }
  if (fixed_ye < 0 && i_ye < 0) {
    std::stringstream msg;
    msg << "### FATAL ERROR in EquationOfState::InitEosConstants" << std::endl
        << "either hydro/eos_ye or hydro/eos_ye_index must be specified."
        << std::endl;
    ATHENA_ERROR(msg);
  }
  T_floor = pin->GetOrAddReal("hydro", "T_floor", Tmin);
  T_ceil = pin->GetOrAddReal("hydro", "T_ceil", Tmax);
  if(T_floor<Tmin){
    T_floor=Tmin;
  }
  // if root processor and zeroth block
  if ((Globals::my_rank == 0) && (pmy_block_->lid == 0)) {
    //std::cout<<Ye<<" Ye\n";
    std::cout<<"Using Ideal gas EOS \n";
  }

  return;
}

