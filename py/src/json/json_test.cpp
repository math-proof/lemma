#include "json.h"
#include <fstream>
#include <iostream>
/** \brief Parse from stream, collect comments and capture error info.
 * Example Usage:
 * $g++ readFromStream.cpp -ljsoncpp -std=c++11 -o readFromStream
 * $./readFromStream
 * // comment head
 * {
 *    // comment before
 *    "key" : "value"
 * }
 * // comment after
 * // comment tail
 */
Json::Value readFromStream(const std::string &json_file) {
	Json::Value root;
	std::ifstream ifs;
	ifs.open(json_file);

	Json::CharReaderBuilder builder;
	builder["collectComments"] = true;
	JSONCPP_STRING errs;
	if (!parseFromStream(builder, ifs, &root, &errs)) {
		std::cout << errs << std::endl;
	}
	return root;
}

int readFromString() {
	const std::string rawJson = R"({"Age": 20, "Name": "colin"})";
	const auto rawJsonLength = static_cast<int>(rawJson.length());
//	constexpr bool shouldUseOldWay = false;
	JSONCPP_STRING err;
	Json::Value root;

//	if (shouldUseOldWay) {
//		Json::Reader reader;
//		reader.parse(rawJson, root);
//	} else {
	Json::CharReaderBuilder builder;
	const std::unique_ptr<Json::CharReader> reader(builder.newCharReader());
	if (!reader->parse(rawJson.c_str(), rawJson.c_str() + rawJsonLength, &root,
			&err)) {
		std::cout << "error" << std::endl;
		return EXIT_FAILURE;
	}
//	}
	const std::string name = root["Name"].asString();
	const int age = root["Age"].asInt();

	std::cout << name << std::endl;
	std::cout << age << std::endl;
	return EXIT_SUCCESS;
}

//https://open-source-parsers.github.io/jsoncpp-docs/doxygen/index.html
