#set(CMAKE_CXX_STANDARD 14)
###############################################
# Project hbuana
###############################################

#cmake minimum requirement
cmake_minimum_required(VERSION 3.17)
set(CMAKE_CXX_STANDARD 17)

#Project name and version
project ( compare VERSION 1.0.0 LANGUAGES C CXX )

#CMake type
set(CMAKE_BUILD_TYPE Debug)

#External packages
find_package( ROOT COMPONENTS Matrix Hist RIO MathCore Physics Minuit)
# find_package( yaml-cpp REQUIRED)

#set run time output directory as bin
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/bin)

#Add include directories
include_directories(src)
include_directories(include)
# include_directories(${YAML_CPP_INCLUDE_DIR})
#message("hey ${YAML_CPP_INCLUDE_DIR}")
include(${ROOT_USE_FILE})

#Add static librarys
add_library(HBase STATIC src/HBase.cxx)
add_library(Select STATIC src/Select.cxx) 
add_library(PID_analyse STATIC src/PID_analyse.cxx) 
# add_library(HBase_data STATIC src/HBase_data.cxx)

#add executable
# add_executable(hbuana src/main.cxx src/DatManager.cxx src/PedestalManager.cxx src/DacManager.cxx src/config.cxx)
add_executable(Calib src/Calib.cxx src/Tree.cxx)
add_executable(digi src/digitize.cxx src/Tree.cxx)
add_executable(convert src/convert_withdigi.cpp src/Tree.cxx)
add_executable(nCalib src/nCalib.cxx src/Tree.cxx)
# add_executable(satu_correct src/satu_correct.cxx src/Tree.cxx)
add_executable(analyse src/analyse.cxx)
# add_executable(temp_correct src/temp_correct.cxx)
# add_executable(analysev2 src/analysev2.cxx)
# add_executable(maxEnCell src/maxEnCell.cxx)
add_executable(mip src/mip.cxx src/Tree.cxx)
add_executable(ped src/pedestal.cxx src/Tree.cxx)
add_executable(mipdata src/mipdata.cxx src/Tree.cxx)
add_executable(disp src/disp.cxx)
add_executable(disp2d src/disp2d.cxx)
add_executable(decode src/decode.cxx)
add_executable(pid src/PID.cxx)
#link libraries
target_link_libraries(Calib ${ROOT_LIBRARIES})
target_link_libraries(digi ${ROOT_LIBRARIES})
target_link_libraries(nCalib ${ROOT_LIBRARIES})
# target_link_libraries(satu_correct ${ROOT_LIBRARIES})
target_link_libraries(mip ${ROOT_LIBRARIES})
target_link_libraries(ped ${ROOT_LIBRARIES})
target_link_libraries(mipdata ${ROOT_LIBRARIES})
target_link_libraries(analyse ${ROOT_LIBRARIES} Select HBase)
# target_link_libraries(temp_correct ${ROOT_LIBRARIES} HBase)
# target_link_libraries(analysev2 ${ROOT_LIBRARIES} Select HBase)
# target_link_libraries(maxEnCell ${ROOT_LIBRARIES} Select HBase)
target_link_libraries(disp ${ROOT_LIBRARIES})
target_link_libraries(disp2d ${ROOT_LIBRARIES})
target_link_libraries(decode ${ROOT_LIBRARIES})
target_link_libraries(pid ${ROOT_LIBRARIES} HBase PID_analyse)

#Add scripts to make setup.sh to include hbuana into environment
# execute_process(COMMAND cp ${CMAKE_CURRENT_SOURCE_DIR}/config/setup.sh ${PROJECT_BINARY_DIR})
# execute_process(COMMAND sed -i "s:PROJECTHERE:${CMAKE_CURRENT_SOURCE_DIR}:g" ${PROJECT_BINARY_DIR}/setup.sh)
# execute_process(COMMAND chmod +x ${PROJECT_BINARY_DIR}/setup.sh)
