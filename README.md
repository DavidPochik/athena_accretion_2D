Diagnosing issues / testing accretion models in 2D.

Compile line:
```
python configure.py --prob accretion_SingleNR_FixedKappa_2D --eos general/helmholtz_gamma_etot --coord spherical_polar --nscalars 2 -h5double -mpi -hdf5 --hdf5_path=${HDF5_HOME}

```
Execute line (feel free to ignore this):
```
mpiexec -n 256 bin/athena -i athinput.accretion_auto Mach_3.0_RPNS_30_MPNS_1.4_Enue_12.6156_Enueb_18.9234_Tau_0.666666_Mdot_0.7_Lnu_40.txt \
problem/rho_f=8559069.829822928 problem/rho_0=1.671726930916e+11 problem/v_f=-1.301642145460e+09 problem/MachNumber=3.0 time/tlim=7.5e-1 \
output1/dt=3.75e-3 output2/dt=3.75e-3 output4/dt=3.75e-3 mesh/x1min=30.0e5 mesh/x1max=1.0e8 mesh/nx1=256 mesh/nx2=128 mesh/x1rat=1.0137917322212853 \
hydro/eos_file_name=../heos_DIR/helm_table.dat problem/eps_nubar=18.9234 problem/eps_nu=12.6156 problem/GM=1.8585255780000003e+26 problem/L_nubar=40 \
problem/L_nu=40 problem/file=Mach_3.0_RPNS_30_MPNS_1.4_Enue_12.6156_Enueb_18.9234_Tau_0.666666_Mdot_0.7_Lnu_40.txt meshblock/nx1=16 meshblock/nx2=8 \
-d Mach_3.0_RPNS_30_MPNS_1.4_Enue_12.6156_Enueb_18.9234_Tau_0.666666_Mdot_0.7_Lnu_40_DIR
```
