# Troubleshooting
If you have any query or troubleshooting related to the tool add a Github issue which is transparent to everyone and can be tracked easily, or you can write to Ridwan Shariffdeen (ridwan@comp.nus.edu.sg). 

##Known issues

The current PatchWeave implementation fails to run on four cases in the PatchWeave 2020 benchmark set: openjpeg-jasper-buffer-overflow, jasper-openjpeg-buffer-overflow, libsndfile-wavpack-shift-overflow and jasper-openjpeg-null-pointer. Note that we report that PatchWeave generate no patch for these defects in our paper. 

The plausible (but incorrect) patch PatchWeave generates for some examples is compiler 
dependent and possibly machine dependent. 

