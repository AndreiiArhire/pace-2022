# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.19

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Disable VCS-based implicit rules.
% : %,v


# Disable VCS-based implicit rules.
% : RCS/%


# Disable VCS-based implicit rules.
% : RCS/%,v


# Disable VCS-based implicit rules.
% : SCCS/s.%


# Disable VCS-based implicit rules.
% : s.%


.SUFFIXES: .hpux_make_needs_suffix_list


# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /home/andrei/clion/bin/cmake/linux/bin/cmake

# The command to remove a file.
RM = /home/andrei/clion/bin/cmake/linux/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/andrei/Desktop/pace_2022

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/andrei/Desktop/pace_2022/cmake-build-debug

# Include any dependencies generated for this target.
include CMakeFiles/pace_2022.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/pace_2022.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/pace_2022.dir/flags.make

CMakeFiles/pace_2022.dir/main.cpp.o: CMakeFiles/pace_2022.dir/flags.make
CMakeFiles/pace_2022.dir/main.cpp.o: ../main.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/andrei/Desktop/pace_2022/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/pace_2022.dir/main.cpp.o"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/pace_2022.dir/main.cpp.o -c /home/andrei/Desktop/pace_2022/main.cpp

CMakeFiles/pace_2022.dir/main.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/pace_2022.dir/main.cpp.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/andrei/Desktop/pace_2022/main.cpp > CMakeFiles/pace_2022.dir/main.cpp.i

CMakeFiles/pace_2022.dir/main.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/pace_2022.dir/main.cpp.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/andrei/Desktop/pace_2022/main.cpp -o CMakeFiles/pace_2022.dir/main.cpp.s

# Object files for target pace_2022
pace_2022_OBJECTS = \
"CMakeFiles/pace_2022.dir/main.cpp.o"

# External object files for target pace_2022
pace_2022_EXTERNAL_OBJECTS =

pace_2022: CMakeFiles/pace_2022.dir/main.cpp.o
pace_2022: CMakeFiles/pace_2022.dir/build.make
pace_2022: CMakeFiles/pace_2022.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/andrei/Desktop/pace_2022/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable pace_2022"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/pace_2022.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/pace_2022.dir/build: pace_2022

.PHONY : CMakeFiles/pace_2022.dir/build

CMakeFiles/pace_2022.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/pace_2022.dir/cmake_clean.cmake
.PHONY : CMakeFiles/pace_2022.dir/clean

CMakeFiles/pace_2022.dir/depend:
	cd /home/andrei/Desktop/pace_2022/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/andrei/Desktop/pace_2022 /home/andrei/Desktop/pace_2022 /home/andrei/Desktop/pace_2022/cmake-build-debug /home/andrei/Desktop/pace_2022/cmake-build-debug /home/andrei/Desktop/pace_2022/cmake-build-debug/CMakeFiles/pace_2022.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/pace_2022.dir/depend

